import z3
import utils
from utils import basic_types_mapping
from utils import array_types_mapping
from utils import operators_mapping
from utils import UnknownStatementTypeInScope
from cfg_nodes import StartNode
from cfg_nodes import HaltNode
from cfg_nodes import ConditionNode
from cfg_nodes import AssignmentNode
from cfg_nodes import AssertNode


class CFG:
    """Class for representing the CFG"""
    def __init__(self, file_name, function_name):
        self.json_file = file_name
        # Read given JSON data to an object
        self.json_data = utils.read_json(self.json_file)

        self.function_name = function_name
        self.function_return_type = None
        self.variables = {}
        self.start = None
        self.halt = None

    def handle_function_argument(self, argument_subtree):
        """
        Creates z3 object for the function argument, and stores it in variables dictionary
        :param argument_subtree: Subtree of some function argument in AST
        :return: None
        """
        type_string = argument_subtree['children'][0]['text']
        if argument_subtree['children'][1]['type'] == 'IDENTIFIER':
            # Received argument is a regular variable
            variable_name = argument_subtree['children'][1]['text']
            self.variables[variable_name] = basic_types_mapping[type_string](variable_name)
        else:
            # Received argument is an array
            assert argument_subtree['children'][1]['type'] == 'direct_declarator'
            array_name = utils.get_item_by_type(argument_subtree['children'][1]['children'], ['IDENTIFIER'],
                                                check_uniqueness=True)[0]['text']
            self.variables[array_name] = z3.Array(array_name, z3.IntSort(), array_types_mapping[type_string]())

    def handle_declarations_in_scope(self, statements):
        """
        Iterates overt the given scope statements, and for each declaration - creates z3 object for a declared variable,
        and stores it in variables dictionary
        :param statements: list of the scope statements
        :return: None
        This method should be used when the CFG creating algorithm enters a scope, and before it starts to go over the
        scope statements and to build the CFG node (otherwise, some variables may not appear in variables dictionary)
        """
        for statement in statements:
            if statement['type'] == 'declaration':
                sub_items = statement['children']
                variable_place = utils.get_item_by_type(sub_items, ['IDENTIFIER', 'init_declarator',
                                                                    'direct_declarator'], check_uniqueness=True)[0]
                type_string = sub_items[0]['text']
                if variable_place['type'] == 'init_declarator':
                    # If declaration statement also contains an assignment ("int x = exp" or "int arr[2] = {0, 0}"),
                    # take only the variable from the left side of an assignment
                    variable_place = variable_place['children'][0]
                if variable_place['type'] == 'IDENTIFIER':
                    # Declared variable is a regular variable ("int x" or "int x = exp")
                    variable_name = variable_place['text']
                    self.variables[variable_name] = basic_types_mapping[type_string](variable_name)
                else:
                    # Declared variable is an array ("int arr[100]" or "int arr[2] = {0, 0}")
                    assert variable_place['type'] == 'direct_declarator'
                    array_name = utils.get_item_by_type(variable_place['children'], ['IDENTIFIER'],
                                                        check_uniqueness=True)[0]['text']
                    self.variables[array_name] = z3.Array(array_name, z3.IntSort(), array_types_mapping[type_string]())

    def handle_assignment_z3(self, statement):
        """
        Based on received assignment/return statement, extracts z3 object of the left-hand variable, z3 object of the
        assigned expression, z3 object of the expression that represent the index in left-hand array expression,
        and this index subtree. Two last fields will be None if assignment target is not an array element
        :param statement: The root of the AST subtree that represents an assignment
        :return: z3 destination variable object, z3 right-hand expression object,
                z3 object of index in the destination array, subtree of index in the destination array
        """
        store_index = None
        store_index_subtree = None
        if statement['type'] == 'jump_statement':
            # Received statement is "return exp;" - dest should be 'ret', index z3 and subtree not relevant
            dest = basic_types_mapping[self.function_return_type]('ret')
            expression = utils.convert_expression_to_z3(self.variables, statement['children'][1])
        else:
            # Received statement is assignment (may be part of declaration)
            assert statement['type'] == 'assignment_expression' or statement['type'] == 'init_declarator'
            index_place_holder = []
            dest = utils.convert_expression_to_z3(self.variables, statement['children'][0], is_destination=True,
                                                  place_for_index=index_place_holder)
            expression = utils.convert_expression_to_z3(self.variables, statement['children'][2])
            if len(statement['children'][1]['text']) > 1:
                # The assignment also contains some operator (like +=) - the assigned expression should be
                # dest operator expression
                assert len(statement['children'][1]['text']) == 2
                operator_string = statement['children'][1]['text'][0]
                expression = operators_mapping[operator_string](dest, expression)
            if isinstance(dest, z3.ArrayRef):
                # If the assignment destination is some array element, need to return z3 expression and AST subtree
                # for the array index as well
                assert len(index_place_holder) == 2
                store_index = index_place_holder[0]
                store_index_subtree = index_place_holder[1]
        return dest, expression, store_index, store_index_subtree

    def handle_assignment_statement(self, subtree, highest):
        """
        Uses for building of CFG when need to handle an assignment statement
        :param subtree: AST subtree which represents an assignment statement
        :param highest: The highest created node in CFG until this moment
        :return: The node that should be highest from now - the assignment node that the method will create
        """
        if subtree['type'] in ['assignment_expression', 'init_declarator']:
            assignment = subtree
        else:
            sub_items = subtree['children']
            assignment = utils.get_item_by_type(sub_items, ['assignment_expression', 'init_declarator'],
                                                check_uniqueness=True)[0]
        target_z3, source_z3, index_z3, index_subtree = self.handle_assignment_z3(assignment)
        if len(assignment['children'][1]['text']) > 1:
            assert len(assignment['children'][1]['text']) == 2
            expression_subtree = assignment
        else:
            expression_subtree = assignment['children'][2]
        result = AssignmentNode(highest, expression_subtree, source_z3, target_z3, target_index_subtree=index_subtree,
                                target_index_z3=index_z3)
        return result

    def handle_declaration_statement(self, subtree, highest):
        """
        Uses for building of CFG when need to handle a declaration statement - if received statement also contains
        an assignment, handle_assignment_statement method will be called. Otherwise (because all the variables are
        already stored in the variables dictionary), nothing will be done
        :param subtree: AST subtree which represents a declaration statement
        :param highest: The highest created node in CFG until this moment
        :return: The node that should be highest from now (the previous highest created if there was no assignment,
                or the created assignment node)
        """
        sub_items = subtree['children']
        variable_place = utils.get_item_by_type(sub_items, ['IDENTIFIER', 'init_declarator', 'direct_declarator'],
                                                check_uniqueness=True)[0]
        if variable_place['type'] == 'IDENTIFIER' or variable_place['type'] == 'direct_declarator':
            return highest
        else:
            assert variable_place['type'] == 'init_declarator'
            assert variable_place['children'][0]['type'] == 'IDENTIFIER'
            return self.handle_assignment_statement(subtree, highest)

    def handle_while_statement(self, sub_items, highest, start_line):
        """
        Uses for building of CFG when need to handle an iteration statement ("while")
        :param sub_items: List of the sons of the subtree of the root node of the "while" statement subtree
        :param highest: The highest created node in CFG until this moment
        :param start_line: The number of the first line of the "while" statement in the code
        :return: The node that should be highest from now -
                the root condition node of the loop that the method will create
        """
        condition_subtree = utils.get_item_by_type(sub_items, ['relational_expression'], check_uniqueness=True)[0]
        condition_z3 = utils.convert_expression_to_z3(self.variables, condition_subtree)
        code_blocks = utils.get_item_by_type(sub_items,
                                             ['compound_statement', 'expression_statement', 'jump_statement'])
        false_son = highest
        result = ConditionNode(None, false_son, condition_subtree, condition_z3, is_cut_point=True,
                               start_line=start_line)
        true_son = self.handle_scope(code_blocks[0], result)
        result.son_true = true_son
        return result

    def handle_for_statement(self, sub_items, highest, start_line):
        """
        Uses for building of CFG when need to handle an iteration statement ("for")
        :param sub_items: List of the sons of the subtree of the root node of the "for" statement subtree
        :param highest: The highest created node in CFG until this moment
        :param start_line: The number of the first line of the "while" statement in the code
        :return: The node that should be highest from now - the assignment node that represents the loop initialization
        """
        initialization = sub_items[2]
        self.handle_declarations_in_scope([initialization])
        condition_subtree = sub_items[3]['children'][0]
        condition_z3 = utils.convert_expression_to_z3(self.variables, condition_subtree)
        code_block = sub_items[6]
        incrementation = sub_items[4]

        false_son = highest
        condition_node = ConditionNode(None, false_son, condition_subtree, condition_z3, is_cut_point=True,
                                       start_line=start_line)
        incrementation_node = self.handle_scope(incrementation, condition_node)
        initialization_node = self.handle_scope(initialization, condition_node)

        true_son = self.handle_scope(code_block, incrementation_node)
        condition_node.son_true = true_son
        return initialization_node

    def handle_iteration_statement(self, subtree, highest):
        """
        Uses for building of CFG when need to handle an iteration statement ("while" or "for")
        :param subtree: AST subtree which represents an iteration statement and the code block of the statements to be
                executed in the loop
        :param highest: The highest created node in CFG until this moment
        :return: The node that should be highest from now
        """
        sub_items = subtree['children']
        start_line_number = subtree['range']['startLineNumber']

        if sub_items[0]['text'] == 'for':
            return self.handle_for_statement(sub_items, highest, start_line_number)
        else:
            assert sub_items[0]['text'] == 'while'
            return self.handle_while_statement(sub_items, highest, start_line_number)

    def handle_selection_statement(self, subtree, highest):
        """
        Uses for building of CFG when need to handle a conditional statement ("if" or "if...else")
        :param subtree: AST subtree which represents a conditional statement and the code blocks of the statements to be
                executed
        :param highest: The highest created node in CFG until this moment
        :return: The node that should be highest from now - the  condition node that the method will create
        """
        sub_items = subtree['children']
        condition_subtree = utils.get_item_by_type(sub_items, ['relational_expression'], check_uniqueness=True)[0]
        condition_z3 = utils.convert_expression_to_z3(self.variables, condition_subtree)
        code_blocks = utils.get_item_by_type(sub_items,
                                             ['compound_statement', 'expression_statement', 'jump_statement'])
        # If 2 blocks were returned, then its an "if...else" statement, so need to handle both of the blocks.
        # Otherwise, there is no "else" statement, so need to connect the "F" edge to the highest created node
        if len(code_blocks) == 2:
            false_son = self.handle_scope(code_blocks[1], highest)
        else:
            false_son = highest
        true_son = self.handle_scope(code_blocks[0], highest)
        result = ConditionNode(true_son, false_son, condition_subtree, condition_z3)
        return result

    def handle_jump_statement(self, subtree):
        """
        Uses for building of CFG when need to handle a return statement
        :param subtree: AST subtree which represents a return statement
        :return: The node that should be highest from now - the assignment node (ret=exp) that the method will create
        This method doesn't receive a highest created until this moment because all the return statements should point
        to the HALT node
        """
        sub_items = subtree['children']
        assert utils.get_item_by_type(sub_items, 'RETURN', check_uniqueness=True)
        target_z3, source_z3, index_z3, index_subtree = self.handle_assignment_z3(subtree)
        assert index_z3 is None and index_subtree is None
        expression_subtree = sub_items[1]
        self.variables['ret'] = target_z3
        result = AssignmentNode(self.halt, expression_subtree, source_z3, target_z3)
        return result

    def handle_assert_statement(self, subtree, highest):
        """
        Uses for building of CFG when need to handle an assert statement
        :param subtree: AST subtree which represents an assert statement
        :param highest: The highest created node in CFG until this moment
        :return: The node that should be highest from now - the assert node that the method will create
        """
        sub_items = subtree['children']
        assert_items = utils.get_item_by_type(sub_items, ['postfix_expression'], check_uniqueness=True)[0]
        assert_expression_subtree = assert_items['children'][2]
        expression_z3 = utils.convert_expression_to_z3(self.variables, assert_expression_subtree)
        result = AssertNode(highest, assert_expression_subtree, expression_z3)
        return result

    def handle_scope(self, scope, highest_created):
        """
        Receives a scope (by list of the scope statements), goes from the end to the beginning, and handles each
        statement using a relevant method for it according to the statement type
        :param scope: List of the AST subtrees - one for each scope statement
        :param highest_created: The highest created node in CFG until this moment
        :return: The node that should be highest from now - the node that represents the first statement of the scope
        """
        if scope['type'] == 'compound_statement':
            statements = utils.get_item_by_type(scope['children'], ['block_item_list'], check_uniqueness=True)[0]
            # Algorithm requires to build the CFG from the bottom,
            # so need to go over the scope statements also from the end to the beginning
            ordered_statements = list(reversed(statements['children']))
        else:
            ordered_statements = [scope]

        # Find all the variables declared in the current scope, and add them to the variables dictionary
        self.handle_declarations_in_scope(ordered_statements)
        current_highest = highest_created
        for statement in ordered_statements:
            if statement['type'] == 'declaration':
                current_highest = self.handle_declaration_statement(statement, current_highest)
            elif statement['type'] == 'expression_statement':
                if 'text' in statement['children'][0]['children'][0].keys() and \
                        statement['children'][0]['children'][0]['text'] == 'assert':
                    current_highest = self.handle_assert_statement(statement, current_highest)
                else:
                    current_highest = self.handle_assignment_statement(statement, current_highest)
            elif statement['type'] == 'assignment_expression':
                current_highest = self.handle_assignment_statement(statement, current_highest)
            elif statement['type'] == 'selection_statement':
                current_highest = self.handle_selection_statement(statement, current_highest)
            elif statement['type'] == 'jump_statement':
                current_highest = self.handle_jump_statement(statement)
            elif statement['type'] == 'iteration_statement':
                current_highest = self.handle_iteration_statement(statement, current_highest)
            elif statement['type'] == ';':
                pass
            else:
                raise UnknownStatementTypeInScope(f"Not handled type: {statement['type']}")
        return current_highest

    def create_cfg(self):
        """
        Builds a CFG for the received function
        :return: None
        """
        chosen_function_subtree = None
        function_definitions = utils.get_item_by_type(self.json_data['children'], ['function_definition'])
        for func in function_definitions:
            function_type = func['children'][0]['text']
            function_declaration = utils.get_item_by_type(func['children'], ['direct_declarator'],
                                                          check_uniqueness=True)[0]['children']
            function_name = utils.get_item_by_type(function_declaration, ['IDENTIFIER'],
                                                   check_uniqueness=True)[0]['text']
            if function_name == self.function_name:
                # Found a required function
                self.function_return_type = function_type
                chosen_function_subtree = func
                parameters_list_item = utils.get_item_by_type(function_declaration, ['parameter_list'])
                if parameters_list_item:
                    params_items = parameters_list_item[0]['children']
                    func_params = utils.get_item_by_type(params_items, ['parameter_declaration'])
                    for param in func_params:
                        self.handle_function_argument(param)
                break

        function_body = utils.get_item_by_type(chosen_function_subtree['children'], ['compound_statement'],
                                               check_uniqueness=True)[0]
        # The CFG is built from the end to the beginning, so the first node to create is HALT, and the last is START
        self.halt = HaltNode()
        highest_created_node = self.handle_scope(function_body, self.halt)
        self.start = StartNode(highest_created_node)

    def invariants_back_patch(self, paths):
        """
        Uses to assign all the program invariants to the relevant CFG node when they are parsed from the configuration
        file. Assigns q1 to the start node of the CFG, q2 to the halt node of the CFG. All the loop invariants are
        assigned to the relevant condition nodes of the CFG using mapping (based on sorting) between invariants indexes
        and the source code line number of the while/for statements
        :return: None
        """
        utils.write_c_file_with_configuration(self.function_name, self.json_file)
        q1, q2, invariants = utils.extract_configuration_subtrees()
        assert q1 is not None and q2 is not None
        self.start.invariant = q1
        self.halt.invariant = q2
        # Go over all the found paths, get from them all the cut points of the program, and create a set of cut points
        # that are related only to condition (while/for) nodes
        loops_nodes_set = set()
        for path in paths:
            if isinstance(path.start_node, ConditionNode):
                loops_nodes_set.add(path.start_node)
            if isinstance(path.end_node, ConditionNode):
                loops_nodes_set.add(path.end_node)
        # Sort invariants by index, and sort the loops by their line number (the first line of the loop block).
        # This performs a mapping between invariants and loops
        sorted_invariants_tuples = sorted(invariants, key=lambda tup: tup[1])
        sorted_invariants = list(map(lambda tup: tup[0], sorted_invariants_tuples))
        sorted_loops = sorted(loops_nodes_set, key=lambda loop: loop.start_line)
        assert len(sorted_loops) == len(sorted_invariants)
        for index in range(len(sorted_loops)):
            # Assign each invariant to the related loop
            sorted_loops[index].invariant = sorted_invariants[index]
            # Also create an Inv#I (where I is index) object that spacer will be able to use
            invariant_arguments_types = []
            for variable in self.variables.values():
                if isinstance(variable, z3.ArrayRef):
                    invariant_arguments_types.append(z3.ArraySort(variable.domain(), variable.range()))
                else:
                    invariant_arguments_types.append(z3.IntSort())
            invariant_arguments_types.append(z3.BoolSort())
            sorted_loops[index].spacer_invariant = z3.Function(f'Invariant#{sorted_invariants_tuples[index][1]}',
                                                               *invariant_arguments_types)

    def print_variables(self):
        """
        Prints the program variables
        :return: None
        """
        print('PROGRAM VARIABLES:')
        for variable in sorted(self.variables):
            print(variable)
        print('\n\n')
