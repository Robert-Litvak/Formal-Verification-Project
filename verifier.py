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
        utils.v_print('VERIFYING PATHS', verbosity=0)
        utils.v_print(f'Verifying the function "{self.function_name}" from "{".".join(self.json_file.split(".")[:2])}"',
                      verbosity=0)
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
        :return: True if the program was verified, False otherwise
        """
        utils.v_print('VERIFYING USING SPACER WITH MANUAL HORN CLAUSES', verbosity=0)
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

    @staticmethod
    def declare_variables(solver, variables, declared_variables):
        """
        Declares the given variables in a received FixedPoint solver, if were not already declared
        :param solver: FixedPoint solver
        :param variables: List of variables to declare
        :param declared_variables: Set of already declared variables
        :return: None
        """
        variables_to_declare = list(filter(lambda var: str(var) not in declared_variables, variables))
        if variables_to_declare:
            solver.declare_var(*variables_to_declare)
            declared_variables.update(set(map(str, variables_to_declare)))

    @staticmethod
    def declare_invariants(solver, path, declared_invariants):
        """
        Declares the invariants of the given path in a received FixedPoint solver, if were not already declared
        :param solver: FixedPoint solver
        :param path: A path whose invariants need to be declared
        :param declared_invariants: Set of already declared invariants
        :return: None
        """
        invariants_to_declare = []
        if isinstance(path.start_node, ConditionNode):
            if str(path.start_node.spacer_invariant) not in declared_invariants:
                invariants_to_declare.append(path.start_node.spacer_invariant)
        if isinstance(path.end_node, ConditionNode):
            if str(path.end_node.spacer_invariant) not in declared_invariants:
                invariants_to_declare.append(path.end_node.spacer_invariant)

        if invariants_to_declare:
            solver.register_relation(*invariants_to_declare)
            declared_invariants.update(set(map(str, invariants_to_declare)))

    def verify_program_fixed_point(self):
        """
        Verifies the program - generates a set of rules and queries for the paths (according to Floyd proof system),
        and tries to find a proper invariants using the fixed point algorithm
        :return: True if the program was verified, False otherwise
        """
        utils.v_print('VERIFYING USING SPACER WITH FIXED POINT', verbosity=0)
        if list(filter(lambda p: not (isinstance(p.start_node, ConditionNode) or isinstance(p.end_node, ConditionNode)),
                       self.paths)):
            utils.v_print('Cannot use fixed point for programs with paths that do not pass in loops', verbosity=0)
            utils.print_separator_lines()
            return False
        utils.v_print(f'Verifying the function "{self.function_name}" from "{".".join(self.json_file.split(".")[:2])}"',
                      verbosity=0)
        solver = z3.Fixedpoint()
        declared_variables = set()
        declared_invariants = set()
        self.declare_variables(solver, self.variables_list, declared_variables)
        for path in self.paths:
            path.calculate_path_z3_invariants()
            source_invariant = self.get_spacer_source_invariant(path)
            dest_invariant, boolean_state_transformation, new_variables = self.get_spacer_destination_invariant(path)

            self.declare_variables(solver, path.array_tmp_variables + new_variables, declared_variables)
            self.declare_invariants(solver, path, declared_invariants)
            try:
                if not (isinstance(dest_invariant, z3.BoolRef) and str(dest_invariant) == 'True'):
                    solver.rule(dest_invariant, [source_invariant, path.start_invariant, path.reachability_condition,
                                                 path.array_constraint, boolean_state_transformation])
                else:
                    solver.query(source_invariant, path.start_invariant, path.reachability_condition,
                                 path.array_constraint, z3.Not(path.mapped_end_invariant))
            except z3.z3types.Z3Exception as error:
                utils.v_print(f'Fixed Point solver failed with error', verbosity=0)
                utils.v_print(f'The error:\n{error}', verbosity=1)
                utils.print_separator_lines()
                return False

        utils.fixed_point_prove(solver, self.variables_list)
        return True
