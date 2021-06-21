import z3
import utils
from cfg_nodes import StartNode
from cfg_nodes import AssignmentNode
from cfg_nodes import AssertNode


class Path:
    """Class for representing path in CFG"""
    def __init__(self, start_node, end_node, action_items, variables):
        self.start_node = start_node
        self.end_node = end_node
        self.action_items = action_items
        self.variables = variables
        self.logical_variables = {}
        self.reachability_condition, self.state_transformation, self.array_constraint = self.calculate_t_and_r()
        self.path_proved = None

    def calculate_t_and_r(self):
        """
        Calculates paths state transformation, reachability condition and array constraint.
        Reachability condition and array constraint are represented as z3 logic expression.
        State transformation is represented as a dictionary,
        where for each variable (key) appears the transformation expression (value)
        :return: Reachability condition, state transformation, array constraint
        """
        # Initialize R, T and AC: (T = variables), (R = True), (AC = True)
        reachability_condition = z3.simplify(z3.And(True, True))
        state_transformation = {}
        for var in self.variables.values():
            state_transformation[var] = var
        array_constraint = z3.simplify(z3.And(True, True))
        # Index that allows to create each time a new array (during assignment to array) with a unique name
        next_array_index = 0

        current_node = self.start_node
        for action in self.action_items:
            if action is None:
                # Path action item is None for start node, assert nodes, and assignment nodes.
                # For start node and assert nodes - T, R and AC remains the same
                if isinstance(current_node, AssertNode) or isinstance(current_node, StartNode):
                    current_node = current_node.son
                else:
                    assert isinstance(current_node, AssignmentNode)
                    dest = current_node.target_z3
                    value = utils.convert_expression_to_z3(self.variables, current_node.expression_subtree,
                                                           variables_mapping=state_transformation)
                    if current_node.target_index_z3 is None:
                        assert current_node.target_index_subtree is None
                        # Target item of the assignment statement is a regular variable
                        state_transformation[dest] = value
                    else:
                        assert current_node.target_index_subtree is not None
                        # Target item of the assignment statement is an array element
                        index = utils.convert_expression_to_z3(self.variables, current_node.target_index_subtree,
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
                condition = utils.convert_expression_to_z3(self.variables, current_node.condition_subtree,
                                                           variables_mapping=state_transformation)
                if action:
                    reachability_condition = z3.And(reachability_condition, condition)
                    current_node = current_node.son_true
                else:
                    reachability_condition = z3.And(reachability_condition, z3.Not(condition))
                    current_node = current_node.son_false
        return reachability_condition, state_transformation, array_constraint

    def print_path(self):
        """
        Prints all the paths that were found. This method should be used only after the "generate_paths" method.
        For each path, also prints its R, T, q2(T), and the array constraint
        :return: None
        """
        # TODO: print(f'Found {len(self.paths)} paths:')
        print('')
        current_node = self.start_node
        for action in self.action_items:
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

        print('')
        print(f'R is:\t{self.reachability_condition}')
        print(f'Simplified R is:\t{z3.simplify(self.reachability_condition)}')
        print(f'T is:\t{dict(self.state_transformation.items())}')

        if self.start_node.invariant is None:
            start_invariant = z3.simplify(z3.And(True, True))
        else:
            start_invariant =\
                utils.convert_expression_to_z3(self.variables, self.start_node.invariant,
                                               allow_not_defined_variables=True,
                                               logical_variables=self.logical_variables)
        print(f'I_start(vars) is:\t {start_invariant}')
        print(f'Simplified I_start(vars) is:\t {z3.simplify(z3.And(True, start_invariant))}')
        converted_and_mapped_end_invariant =\
            utils.convert_expression_to_z3(self.variables, self.end_node.invariant,
                                           variables_mapping=self.state_transformation,
                                           allow_not_defined_variables=True,
                                           logical_variables=self.logical_variables)
        print(f'I_end(T(vars)) is:\t {converted_and_mapped_end_invariant}')
        print(f'Simplified I_end(T(vars)) is:\t {z3.simplify(z3.And(True, converted_and_mapped_end_invariant))}')
        print(f'Array constraints: {self.array_constraint}')

        floyd_proof = z3.Implies(z3.And(start_invariant, self.reachability_condition, self.array_constraint),
                                 converted_and_mapped_end_invariant)
        self.path_proved = utils.prove(floyd_proof)
        print('\n\n')

        utils.filter_dictionary(self.variables, self.logical_variables.keys())
