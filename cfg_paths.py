import z3
import utils
from cfg_nodes import StartNode
from cfg_nodes import HaltNode
from cfg_nodes import ConditionNode
from cfg_nodes import AssignmentNode
from cfg_nodes import AssertNode


class CfgPaths:
    """Class for working with the CFG paths"""
    def __init__(self, cfg):
        self.cfg = cfg
        self.logical_variables = {}
        self.configuration_ast = None
        self.paths = []
        self.stack = []
        self.cut_points = []
        self.cut_points_queue = [(self.cfg.start, None)]
        self.not_proved_paths = []

    def recursive_paths(self, sub_cfg, path_root):
        """
        Searches recursively for paths to the next cut points
        :param sub_cfg: CFG node to start searching from it (it is the second node of each path that will be found)
        :param path_root: First node of each path that will be found
        :return: None
        """
        # If node is a cut point, we'll check whether it was added into the list and if no - add it and finish the path
        if sub_cfg.is_cut_point:
            # Another path is found - store the first node of the path, and the action items that represent the path
            self.paths.append((path_root, sub_cfg, self.stack.copy()))
            if sub_cfg not in self.cut_points:
                self.cut_points.append(sub_cfg)
                if isinstance(sub_cfg, ConditionNode):
                    self.cut_points_queue += [(sub_cfg, 'T'), (sub_cfg, 'F')]
                elif isinstance(sub_cfg, AssertNode):
                    self.cut_points_queue += [(sub_cfg, 'M')]
                else:
                    assert isinstance(sub_cfg, HaltNode)
            return
        # If node is an assignment, just keep going with the path
        if isinstance(sub_cfg, AssignmentNode):
            self.stack.append(None)
            self.recursive_paths(sub_cfg.son, path_root)
            self.stack.pop()
        # If node is a condition, generate 2 paths from here: one true and one false
        elif isinstance(sub_cfg, ConditionNode) and not sub_cfg.is_cut_point:
            self.stack.append(False)
            self.recursive_paths(sub_cfg.son_false, path_root)
            self.stack.pop()
            self.stack.append(True)
            self.recursive_paths(sub_cfg.son_true, path_root)
            self.stack.pop()

    def find_paths_to_the_next_cut_points(self, path_root, direction):
        """
        Finds basic paths to all the closest next cut points
        :param path_root: CFG node to start searching from it
        :param direction: The direction to use from the first node of the path
        :return: None
        """
        # Assumption, that start node can be only at the start of the path
        if isinstance(path_root, StartNode):
            self.stack.append(None)
            self.recursive_paths(path_root.son, path_root)
            self.stack.pop()
        elif direction is not None:
            assert direction in ['T', 'F', 'M']
            # Direction T means that we current node is condition node (usually while or for)
            # and we choose path where condition is satisfied
            if direction == 'T':
                self.stack.append(True)
                self.recursive_paths(path_root.son_true, path_root)
                self.stack.pop()
            # Direction F means that we current node is condition node
            # and we choose path where condition is not satisfied
            elif direction == 'F':
                self.stack.append(False)
                self.recursive_paths(path_root.son_false, path_root)
                self.stack.pop()
            # Direction M means that we current node is not a condition node (usually assert)
            else:
                # direction == 'M'
                self.stack.append(None)
                self.recursive_paths(path_root.son, path_root)
                self.stack.pop()

    def generate_paths(self):
        """
        Finds all the basic paths of the program. The paths will be stored in self.paths
        :return: None
        """
        # Wrapper for path search algorithm. Here we start BFS search for cut points.
        # While set is not empty, we will take out cut point and generate paths from it. If on a path way we will find
        # cut point that wasn't fond yet, we will add it to the set.
        while self.cut_points_queue:
            current_cut_point = self.cut_points_queue[0]
            self.cut_points_queue.remove(current_cut_point)
            self.find_paths_to_the_next_cut_points(path_root=current_cut_point[0], direction=current_cut_point[1])

    def calculate_t_and_r(self, path_root, path):
        """
        Calculates paths state transformation, reachability condition and array constraint.
        Reachability condition and array constraint are represented as z3 logic expression.
        State transformation is represented as a dictionary,
        where for each variable (key) appears the transformation expression (value)
        :param path_root: First node of the given path
        :param path: Path represented as a list of action items
        :return: Reachability condition, state transformation, array constraint
        """
        # Initialize R, T and AC: (T = variables), (R = True), (AC = True)
        reachability_condition = z3.simplify(z3.And(True, True))
        state_transformation = {}
        for var in self.cfg.variables.values():
            state_transformation[var] = var
        array_constraint = z3.simplify(z3.And(True, True))
        # Index that allows to create each time a new array (during assignment to array) with a unique name
        next_array_index = 0

        current_node = path_root
        for action in path:
            if action is None:
                # Path action item is None for start node, assert nodes, and assignment nodes.
                # For start node and assert nodes - T, R and AC remains the same
                if isinstance(current_node, AssertNode) or isinstance(current_node, StartNode):
                    current_node = current_node.son
                else:
                    assert isinstance(current_node, AssignmentNode)
                    dest = current_node.target_z3
                    value = utils.convert_expression_to_z3(self.cfg.variables, current_node.expression_subtree,
                                                           variables_mapping=state_transformation)
                    if current_node.target_index_z3 is None:
                        assert current_node.target_index_subtree is None
                        # Target item of the assignment statement is a regular variable
                        state_transformation[dest] = value
                    else:
                        assert current_node.target_index_subtree is not None
                        # Target item of the assignment statement is an array element
                        index = utils.convert_expression_to_z3(self.cfg.variables, current_node.target_index_subtree,
                                                               variables_mapping=state_transformation)
                        new_array = z3.Array(f'TMP$ARR_{next_array_index}', dest.domain(), dest.range())
                        deepest_dest_mapping = utils.get_chain_deepest_mapping(state_transformation, dest)
                        array_constraint = z3.And(array_constraint,
                                                  z3.Store(deepest_dest_mapping, index, value) == new_array)
                        state_transformation[deepest_dest_mapping] = new_array
                        next_array_index += 1
                    current_node = current_node.son
            else:
                # Path action item is True/False for condition nodes
                condition = utils.convert_expression_to_z3(self.cfg.variables, current_node.condition_subtree,
                                                           variables_mapping=state_transformation)
                if action:
                    reachability_condition = z3.And(reachability_condition, condition)
                    current_node = current_node.son_true
                else:
                    reachability_condition = z3.And(reachability_condition, z3.Not(condition))
                    current_node = current_node.son_false
        return reachability_condition, state_transformation, array_constraint

    def invariants_back_patch(self):
        """
        Uses to assign all the program invariants to the relevant CFG node when they are parsed from the configuration
        file. Assigns q1 to the start node of the CFG, q2 to the halt node of the CFG. All the loop invariants are
        assigned to the relevant condition nodes of the CFG using mapping (based on sorting) between invariants indexes
        and the source code line number of the while/for statements
        :return: None
        """
        utils.write_c_file_with_configuration(self.cfg.function_name, self.cfg.json_file)
        q1, q2, invariants = utils.extract_configuration_subtrees()
        self.cfg.start.invariant = q1
        self.cfg.halt.invariant = q2
        # Go over all the found paths, get from them all the cut points of the program, and create a set of cut points
        # that are related only to condition (while/for) nodes
        loops_nodes_set = set()
        for start_node, finish_node, path in self.paths:
            if isinstance(start_node, ConditionNode):
                loops_nodes_set.add(start_node)
            if isinstance(finish_node, ConditionNode):
                loops_nodes_set.add(finish_node)
        # Sort invariants by index, and sort the loops by their line number (the first line of the loop block).
        # This performs a mapping between invariants and loops
        sorted_invariants_tuples = sorted(invariants, key=lambda tup: tup[1])
        sorted_invariants = list(map(lambda tup: tup[0], sorted_invariants_tuples))
        sorted_loops = sorted(loops_nodes_set, key=lambda loop: loop.start_line)
        assert len(sorted_loops) == len(sorted_invariants)
        # Assign each invariant to the related loop
        for index in range(len(sorted_loops)):
            sorted_loops[index].invariant = sorted_invariants[index]

    def print_paths(self):
        """
        Prints all the paths that were found. This method should be used only after the "generate_paths" method.
        For each path, also prints its R, T, q2(T), and the array constraint
        :return: None
        """
        print(f'Found {len(self.paths)} paths:')
        for first, last, path in self.paths:
            print('')
            current_node = first
            for action in path:
                print(current_node)
                if action is None:
                    current_node = current_node.son
                else:
                    print(action)
                    if action:
                        current_node = current_node.son_true
                    else:
                        current_node = current_node.son_false
            assert current_node.is_cut_point
            print(current_node)

            r, t, array_constraint = self.calculate_t_and_r(first, path)
            print('')
            print(f'R is:\t{r}')
            print(f'Simplified R is:\t{z3.simplify(r)}')
            print(f'T is:\t{dict(t.items())}')

            if first.invariant is None:
                start_invariant = z3.simplify(z3.And(True, True))
            else:
                start_invariant =\
                    utils.convert_expression_to_z3(self.cfg.variables, first.invariant,
                                                   allow_not_defined_variables=True,
                                                   logical_variables=self.logical_variables)
            print(f'I_start(vars) is:\t {start_invariant}')
            print(f'Simplified I_start(vars) is:\t {z3.simplify(z3.And(True, start_invariant))}')
            converted_and_mapped_end_invariant =\
                utils.convert_expression_to_z3(self.cfg.variables, last.invariant, variables_mapping=t,
                                               allow_not_defined_variables=True,
                                               logical_variables=self.logical_variables)
            print(f'I_end(T(vars)) is:\t {converted_and_mapped_end_invariant}')
            print(f'Simplified I_end(T(vars)) is:\t {z3.simplify(z3.And(True, converted_and_mapped_end_invariant))}')
            print(f'Array constraints: {array_constraint}')

            floyd_proof = z3.Implies(z3.And(start_invariant, r, array_constraint), converted_and_mapped_end_invariant)
            if not utils.prove(floyd_proof):
                self.not_proved_paths.append((first, last, path))
            print('\n\n')

            utils.filter_dictionary(self.cfg.variables, self.logical_variables.keys())
