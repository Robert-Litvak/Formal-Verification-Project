import z3
import utils
from cfg_nodes import ConditionNode
from cfg import CFG
from path_finder import PathFinder


class Verifier:
    def __init__(self, json_file, function_name):
        self.json_file = json_file
        self.function_name = function_name
        self.cfg = CFG(self.json_file, self.function_name)
        self.variables_list = None
        self.paths = None

        self.build_cfg_and_paths()

    def build_cfg_and_paths(self):
        """
        Builds the CFG, and finds all the paths in it
        :return: None
        """
        self.cfg.create_cfg()
        self.variables_list = list(self.cfg.variables.values())
        path_finder = PathFinder(self.cfg)
        path_finder.generate_paths()
        self.paths = path_finder.paths
        self.cfg.invariants_back_patch(self.paths)

    def verify_paths(self):
        """
        Goes over all the paths in CFG, and tries to prove them according to Floyd proof system
        :return: None
        """
        utils.v_print(f'Found {len(self.paths)} paths:', verbosity=1)
        for path in self.paths:
            path.print_path()
            path.verify_path()
        self.cfg.print_variables()

        not_proved_paths = list(filter(lambda cfg_path: not cfg_path.path_proved, self.paths))
        if not not_proved_paths:
            utils.v_print('PROGRAM IS SUCCESSFULLY PROVED', verbosity=0)
        else:
            utils.v_print('FAILED TO PROVE THE PROGRAM', verbosity=0)
            utils.v_print('SEE THE FOLLOWING PATHS:', verbosity=1)
            for path in not_proved_paths:
                utils.v_print(f'Path begin at: {path.start_node}', verbosity=1)
                utils.v_print(f'Path ends at {path.end_node}', verbosity=1)
                utils.v_print(f'Path action items are {path.action_items}', verbosity=1)

    def get_spacer_source_invariant(self, path):
        """
        If the start node of the path is a loop condition node, returns the attached to it Z3 invariant function,
        otherwise returns True (Z3)
        :param path: Path to get its start invariant
        :return: The start invariant of the path
        """
        if isinstance(path.start_node, ConditionNode):
            return path.start_node.spacer_invariant(*self.variables_list)
        else:
            # True
            return utils.list_to_z3_and([])

    def get_spacer_destination_invariant(self, path):
        """
        If the end node of the path is a loop condition node, returns the attached to it Z3 invariant function,
        otherwise returns True (Z3). Also returns a list of new temporary variables required to use in the invariant,
        and the boolean representation of state transformation
        :param path: Path to get its end invariant
        :return: The end invariant of the path, State transformation (as boolean expression),
                New variables for the invariant
        """
        new_variables = []
        boolean_state_transformations = []
        if isinstance(path.end_node, ConditionNode):
            for var in self.variables_list:
                # For each program variable "var", create a temporary "var$IN$Invariant#I" variable
                new_var_name = str(var) + '$IN$' + str(path.end_node.spacer_invariant.name())
                if isinstance(var, z3.ArrayRef):
                    current_new_var = z3.Array(new_var_name, var.domain(), var.range())
                else:
                    current_new_var = z3.Int(new_var_name)

                new_variables.append(current_new_var)
                boolean_state_transformations.append(current_new_var == path.state_transformation[var])

            dest_invariant = path.end_node.spacer_invariant(*new_variables)
        else:
            dest_invariant = utils.list_to_z3_and([])           # True

        return dest_invariant, utils.list_to_z3_and(boolean_state_transformations), new_variables

    def verify_program(self):
        """
        Verifies the program - generates a set of rules for the paths (according to Floyd proof system),
        and tries to find a proper invariants using horn clauses
        :return: None
        """
        utils.v_print(f'Verifying the function "{self.function_name}" from "{".".join(self.json_file.split(".")[:2])}"',
                      verbosity=0)
        rules = []
        for path in self.paths:
            path.calculate_path_z3_invariants()
            source_invariant = self.get_spacer_source_invariant(path)
            dest_invariant, boolean_state_transformations, new_variables = self.get_spacer_destination_invariant(path)

            if not (isinstance(path.mapped_end_invariant, z3.BoolRef) and str(path.mapped_end_invariant) == 'True'):
                # If the given by user invariant is not a trivial one (True), use it for the path
                rules.append(z3.ForAll(self.variables_list + path.array_tmp_variables,
                                       z3.Implies(z3.And(source_invariant, path.start_invariant,
                                                         path.reachability_condition, path.array_constraint),
                                                  path.mapped_end_invariant)))
            if not (isinstance(dest_invariant, z3.BoolRef) and str(dest_invariant) == 'True'):
                # If there is no spacer destination invariant function for the end node of the path,
                # don't need to create a rule. Otherwise, append it to the rules list
                rules.append(z3.ForAll(self.variables_list + path.array_tmp_variables + new_variables,
                                       z3.Implies(z3.And(source_invariant, path.start_invariant,
                                                         path.reachability_condition, path.array_constraint,
                                                         boolean_state_transformations),
                                                  dest_invariant)))

        return utils.horn_prove(rules, self.variables_list)
