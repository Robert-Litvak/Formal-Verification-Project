import os
import sys
import re
import operator
import subprocess
import argparse
import json
import z3
from configparser import ConfigParser


# Exceptions
class ItemOfThisTypeShouldBeUniqueInList(Exception):
    pass


class UnknownStatementTypeInScope(Exception):
    pass


class VerbosityCannotBeSetMoreThanOnce(Exception):
    pass


class InvalidVerbosityLevel(Exception):
    pass


# Logical keywords
logical_keywords = ['implies', 'forall', 'exists']


# Dictionaries used for mapping of types and operators
basic_types_mapping = {'int': z3.Int, 'bool': z3.Bool}
array_types_mapping = {'int': z3.IntSort, 'bool': z3.BoolSort}
operators_mapping = {'!': (lambda op: z3.Not(op)), '||': (lambda op1, op2: z3.Or(op1, op2)),
                     '&&': (lambda op1, op2: z3.And(op1, op2)), '+': operator.add, '-': operator.sub, '*': operator.mul,
                     '/': operator.truediv, '%': operator.mod, '^': operator.xor, '<': operator.lt, '<=': operator.le,
                     '==': operator.eq, '!=': operator.ne, '>=': operator.ge, '>': operator.gt}


# Program verbosity parameters
verbosity_levels = [0, 1, 2, 3]
program_verbosity = -1


def set_verbosity(level):
    global program_verbosity
    if level not in verbosity_levels:
        raise InvalidVerbosityLevel(f'Invalid verbosity {level}. The only allowed levels: {verbosity_levels}')
    if program_verbosity != -1:
        raise VerbosityCannotBeSetMoreThanOnce

    program_verbosity = level


def v_print(string, verbosity):
    if verbosity <= program_verbosity:
        print(string)


def read_json(json_file_name):
    """
    Reads JSON file and returns an object that represents the AST
    :param json_file_name: Name of the JSON file to read
    :return: Object that represents the AST
    """
    with open(json_file_name, 'r') as file_object:
        result = json.load(file_object)
    return result


def parse_arguments():
    """
    Parses program command line arguments
    :return: object containing a field for each parsed argument
    """
    parser = argparse.ArgumentParser(description='CFG Builder arguments', add_help=True, allow_abbrev=True)
    parser.add_argument('-json_file', help='The name of the JSON file to get an AST from')
    parser.add_argument('-function_name', help='Name of the function that should be verified')
    parser.add_argument('-all_tests', action='store_const', const=True,
                        help='Run verifier on all the available functions from all the available files')
    parser.add_argument('-paths',  action='store_const', const=True, help='Verify the program by paths')
    parser.add_argument('-verbosity', type=int, choices=verbosity_levels, default=0,
                        help='The higher the verbosity level - the more information will be displayed')
    return parser.parse_args(sys.argv[1:])


def filter_dictionary(dictionary, keys_to_remove):
    """
    Filters the received dictionary according to the received keys - the items that their keys appear in "filter_keys"
    will be removed from the "dictionary"
    :param dictionary: Dictionary to filter
    :param keys_to_remove: Keys to remove from the dictionary
    :return: None
    """
    for key in keys_to_remove:
        if key in dictionary.keys():
            del dictionary[key]


def get_function_configuration_from_ini(function_name, json_file):
    """
    Parses ".ini" configuration file, and returns the configuration as a dictionary.
    The file name of a configuration file is deduced from the file name of JSON AST of the program
    :param function_name: The name of the function that the verifier trying to prove
    :param json_file: The file name of JSON AST of the program
    :return: Dictionary with a configuration that appears in the relevant ".ini" file in a section "[function_name]"
    """
    config_file_name = re.match(r'(\w+)\.c\.ast\.json$', os.path.basename(json_file)).group(1) + '.ini'
    config_file_path = os.path.join('benchmarks', 'config_files', config_file_name)
    parser = ConfigParser()
    parser.read(config_file_path)
    assert parser.has_section(function_name)
    return dict(parser.items(function_name))


def write_c_file_with_configuration(function_name, json_file):
    """
    Uses a configuration from the relevant ".ini" file, and creates a temporary c file of the following format:
    void configuration(){
        bool q1 = ...;
        bool q2 = ...;
        bool invariant_1 = ...;
        ...
    }
    This file will be parsed using JSON in order to receive the AST of the configuration parameters
    :param function_name: The name of the function that the verifier trying to prove
    :param json_file: The file name of JSON AST of the program
    :return: None
    """
    configuration = get_function_configuration_from_ini(function_name, json_file)
    with open('temp_configuration.c', 'w') as c_config_file:
        c_config_file.write('void configuration(){\n')
        for key, value in configuration.items():
            c_config_file.write(f'\tbool {key} = {value};\n')
        c_config_file.write('}\n')


def extract_configuration_subtrees():
    """
    Uses (already) created "temp_configuration.c" file in order to extract the AST subtrees of q1, q2, and all the
    invariants
    :return: AST subtree of q1, AST subtree of q2, list of AST subtrees of all the invariants
    """
    # Use "node.exe" to parse the previously generated 'temp_configuration.c'
    parsing_command = ['node.exe', os.path.join('ext', 'sindarin.js'), 'parse', 'temp_configuration.c']
    parsing_process = subprocess.Popen(parsing_command)
    parsing_process.wait()
    v_print('', verbosity=0)
    configuration_ast = read_json('temp_configuration.c.ast.json')
    # Remove temporary "c" and "json" files that used to get the configuration
    os.remove('temp_configuration.c')
    os.remove('temp_configuration.c.ast.json')
    # Get the list of configuration declarations from the generated AST
    all_statements = configuration_ast['children'][0]['children'][2]['children'][1]['children']
    q1 = None
    q2 = None
    invariants = []
    for statement in all_statements:
        name = statement['children'][1]['children'][0]['text']
        expression = statement['children'][1]['children'][2]
        if name == 'q1':
            q1 = expression
        elif name == 'q2':
            q2 = expression
        else:
            match_object = re.match(r'invariant_(\d+)$', name)
            assert match_object
            invariants.append((expression, int(match_object.group(1))))
    return q1, q2, invariants


def get_item_by_type(items_list, required_types, check_uniqueness=False):
    """
    Finds required nodes in given AST (typically children) nodes list
    :param items_list: List of AST nodes
    :param required_types: List of AST node types to filter the nodes -
            only the nodes whose types appears in the list will be returned
    :param check_uniqueness: If check_uniqueness==True, checks that the result list contain exactly one element
    :return: List of items from items_list whose type appears in 'required_types'
    """
    result = list(filter(lambda item: item['type'] in required_types, items_list))
    if check_uniqueness and len(result) != 1:
        raise ItemOfThisTypeShouldBeUniqueInList
    return result


def get_chain_deepest_mapping(mapping, start_key):
    """
    Finds the longest mapping chain that starts from the start_key and returns the last element of the chain
    :param mapping: Dictionary that represents variables mapping (typically, state transformation)
    :param start_key: A key to start a chain search from
    :return: The last element of the found mapping chain
    Example:
    If state_transformation is {arr: TMP$ARR_0, i: i, tmp: TMP$ARR_3[i], TMP$ARR_0: TMP$ARR_1, TMP$ARR_1: TMP$ARR_2,
                                TMP$ARR_2: TMP$ARR_3, TMP$ARR_3: TMP$ARR_4, TMP$ARR_4: TMP$ARR_5}
    Then get_chain_deepest_mapping(state_transformation, arr)
    will find the chain arr->TMP$ARR_0->TMP$ARR_1->TMP$ARR_2->TMP$ARR_3->TMP$ARR_4->TMP$ARR_5
    and return TMP$ARR_5
    """
    assert start_key in mapping.keys()
    # If there are no chain, the first element will be mapped to itself
    if start_key == mapping[start_key]:
        return mapping[start_key]
    result = mapping[start_key]
    while result in mapping.keys():
        result = mapping[result]
    return result


def convert_variable_to_z3(variables_dictionary, expression, variables_mapping, allow_not_defined_variables,
                           logical_variables):
    """See the description of convert_expression_to_z3"""
    item_text = expression['text']
    if allow_not_defined_variables and (item_text not in variables_dictionary.keys()):
        # Variable is logical - doesn't appear in the code, but appears in the q1/q2/invariants
        variables_dictionary[item_text] = z3.Int(item_text)
        logical_variables[item_text] = z3.Int(item_text)
    # Get the stored z3 object of the variable
    item_z3_object = variables_dictionary[item_text]
    # If mapping required, do so using variables_mapping dictionary
    if variables_mapping and item_z3_object in variables_mapping:
        return variables_mapping[item_z3_object]
    else:
        return item_z3_object


def convert_array_to_z3(variables_dictionary, expression, variables_mapping, is_destination, place_for_index,
                        allow_not_defined_variables, logical_variables):
    """See the description of convert_expression_to_z3"""
    items = expression['children']
    array_name = items[0]['text']
    # Doesn't pass "is_destination" or "place_for_index", because they are not relevant inside of the recursion
    array_index = convert_expression_to_z3(variables_dictionary, items[2], variables_mapping,
                                           allow_not_defined_variables=allow_not_defined_variables,
                                           logical_variables=logical_variables)
    array_object = variables_dictionary[array_name]
    # If array expression is on the left side of assignment statement, return the array object to user, and put into
    # "place_for_index" the index expression and subtree - z3.Store will be handled after
    if is_destination:
        result = array_object
        place_for_index += [array_index, items[2]]
    else:
        # If mapping required, do so using variables_mapping dictionary
        # (arrays require to find the last element of mapping chain)
        if variables_mapping and array_object in variables_mapping:
            result = get_chain_deepest_mapping(variables_mapping, array_object)[array_index]
        else:
            result = array_object[array_index]
    return result


def convert_complex_logic_to_z3(variables_dictionary, expression, variables_mapping, logical_variables):
    """See the description of convert_expression_to_z3"""
    # Name of the logical operator
    keyword = expression['children'][0]['text']
    assert keyword in logical_keywords
    # Arguments for the logical operator
    arguments = get_item_by_type(expression['children'], ['argument_expression_list'],
                                 check_uniqueness=True)[0]['children']
    # All of the logical operators we use get 2 arguments
    left_expression = arguments[0]
    right_expression = arguments[2]
    left_z3 = convert_expression_to_z3(variables_dictionary, left_expression, variables_mapping,
                                       allow_not_defined_variables=True, logical_variables=logical_variables)
    right_z3 = convert_expression_to_z3(variables_dictionary, right_expression, variables_mapping,
                                        allow_not_defined_variables=True, logical_variables=logical_variables)
    if keyword == 'implies':
        return z3.Implies(left_z3, right_z3)
    if keyword == 'forall':
        return z3.ForAll([left_z3], right_z3)
    if keyword == 'exists':
        return z3.Exists([left_z3], right_z3)


def convert_unary_operation_to_z3(variables_dictionary, expression, variables_mapping, allow_not_defined_variables,
                                  logical_variables):
    """See the description of convert_expression_to_z3"""
    operand = convert_expression_to_z3(variables_dictionary, expression['children'][1], variables_mapping,
                                       allow_not_defined_variables=allow_not_defined_variables,
                                       logical_variables=logical_variables)
    expression_operator = expression['children'][0]['text']
    if expression_operator == '-':
        return -operand
    else:
        return operators_mapping[expression_operator](operand)


def convert_binary_operation_to_z3(variables_dictionary, expression, variables_mapping, allow_not_defined_variables,
                                   logical_variables):
    """See the description of convert_expression_to_z3"""
    operand_1 = convert_expression_to_z3(variables_dictionary, expression['children'][0], variables_mapping,
                                         allow_not_defined_variables=allow_not_defined_variables,
                                         logical_variables=logical_variables)
    operand_2 = convert_expression_to_z3(variables_dictionary, expression['children'][2], variables_mapping,
                                         allow_not_defined_variables=allow_not_defined_variables,
                                         logical_variables=logical_variables)
    expression_operator = expression['children'][1]['text']
    if expression['type'] == 'assignment_expression':
        assert len(expression_operator) == 2
        expression_operator = expression_operator[0]
    return operators_mapping[expression_operator](operand_1, operand_2)


def convert_expression_to_z3(variables_dictionary, expression, variables_mapping=None, is_destination=False,
                             place_for_index=None, allow_not_defined_variables=False, logical_variables=None):
    """
    Converts expression (represented by the root of its subtree in AST) to z3 object which represents the same
    expression
    :param variables_dictionary: Dictionary that maps every variable name to its z3 object
    :param expression: AST node whose subtree represents an expression
    :param variables_mapping: Dictionary that represents variables mapping (typically, state transformation)
    :param is_destination: If is_destination==True, then given expression is placed on the left side of "="
            in some assignment command
    :param place_for_index: Relevant for arrays only - if expression represent expression of type arr[exp],
            and it is placed on the left side of "=" in some assignment command, then z3 object representing the
            index expression will be stored in place_for_index[0],
            and the index expression AST subtree will be stored in place_for_index[1]
    :param allow_not_defined_variables: If allow_not_defined_variables==True, then if expression contains variable that
            is not appears in variables_dictionary, no error will be caused
    :param logical_variables: a dictionary to store logical variables (variables that didn't appear in the program, but
            appeared in the specification
    :return: z3 object that represents the given expression
    """
    if expression['type'] == 'CONSTANT':
        # Received expression is a number
        return int(expression['text'])

    elif expression['type'] == 'IDENTIFIER' and (expression['text'] == 'true' or expression['text'] == 'false'):
        # Received expression is "true" or "false"
        item_text = expression['text']
        if item_text == 'true':
            return z3.simplify(z3.And(True, True))
        else:
            assert item_text == 'false'
            return z3.simplify(z3.And(False, False))

    elif expression['type'] == 'IDENTIFIER':
        # Received expression is a variable name
        return convert_variable_to_z3(variables_dictionary, expression, variables_mapping, allow_not_defined_variables,
                                      logical_variables)

    elif expression['type'] == 'postfix_expression' and expression['children'][1]['text'] == '[':
        assert expression['children'][3]['text'] == ']'
        # Received expression represents access to some array
        return convert_array_to_z3(variables_dictionary, expression, variables_mapping, is_destination, place_for_index,
                                   allow_not_defined_variables, logical_variables)

    elif expression['type'] == 'postfix_expression' and expression['children'][1]['text'] == '(':
        # Received expression represents "implies(...)", "forall(...)" or "exists(...)"
        assert expression['children'][3]['text'] == ')'
        return convert_complex_logic_to_z3(variables_dictionary, expression, variables_mapping, logical_variables)

    elif expression['type'] == 'primary_expression':
        # Received expression is wrapped by brackets
        expression_inside_brackets =\
            convert_expression_to_z3(variables_dictionary, expression['children'][1], variables_mapping, is_destination,
                                     place_for_index, allow_not_defined_variables, logical_variables)
        return expression_inside_brackets

    elif expression['type'] == 'unary_expression':
        # Received expression represents some unary operation
        return convert_unary_operation_to_z3(variables_dictionary, expression, variables_mapping,
                                             allow_not_defined_variables, logical_variables)

    else:
        # Received expression represents some binary operation
        return convert_binary_operation_to_z3(variables_dictionary, expression, variables_mapping,
                                              allow_not_defined_variables, logical_variables)


def list_to_z3_and(items):
    """
    Converts a list of boolean z3 expressions to a single z3.And(...) between the expressions
    :param items: A list of boolean z3 expressions
    :return: z3.And object operating on all the received expressions
    """
    if not items:
        return z3.simplify(z3.And(True, True))
    elif len(items) == 1:
        return items[0]
    else:
        return z3.And(*items)


def process_rule_string(rule_string, variables):
    """
    Converts the invariant string to a more readable format
    :param rule_string: The string representing the invariants
    :param variables: List of the program variables
    :return: Processed string
    """
    result = rule_string
    # Change all the "Var(\d+)" Z3 variables names to the corresponding program variables
    for index in range(len(variables)):
        result = re.sub(fr'Var\({index}\)', str(variables[index]), result)
    # Change all the "+ -1*expression" subtract representation to the regular "- expression" representation
    result = re.sub(r'\+ -1\*', '- ', result)
    result = re.sub(r'Or\(Not\((.+)\), (.+)\)', r'\1 -> \2', result)
    return result


def prove(formula):
    """
    Checks if the given formula is a tautology, using z3.
    If the formula is a tautology, will v_print "PROVED",
    Otherwise will v_print "FAILED TO PROVE. ASSIGNMENT:" with the assignment (counter-example)
    :param formula: z3 formula object
    :return: True if the formula was successfully proved, False otherwise
    """
    solver = z3.Solver()
    solver.push()
    solver.add(z3.Not(formula))
    if solver.check() == z3.unsat:
        v_print('PROVED', verbosity=1)
        result = True
    else:
        v_print('FAILED TO PROVE. ASSIGNMENT:', verbosity=0)
        model = solver.model()
        for declaration in model.decls():
            v_print(f'{declaration.name()} = {model[declaration]}', verbosity=0)
        result = False
    solver.pop()
    return result


def horn_prove(rules, variables=None):
    """
    Receives a list of rules (which represent horn clauses), and tries to find an invariant that satisfies the rules.
    All the received rules will be printed in python z3 format.
    If result is success (sat), all the Var(<i>) variable names will be replaced with actual variables from the program
    :param rules: A list of rules which represent horn clauses
    :param variables: Variables list of the verifier
    :return: None
    """
    solver = z3.SolverFor('HORN')
    v_print('Adding rules:', verbosity=1)
    for rule in rules:
        v_print(rule, verbosity=1)
        solver.add(rule)
        v_print('#' * 113, verbosity=1)
    result = solver.check()
    if result == z3.sat:
        v_print('PROVED', verbosity=0)
        model = solver.model()
        if model.decls():
            v_print('THE INVARIANTS:', verbosity=0)
            for declaration in model.decls():
                value = process_rule_string(str(model[declaration]), variables)
                v_print(f'{declaration.name()} = {value}', verbosity=0)
        else:
            v_print('No invariants required', verbosity=0)
    else:
        v_print('FAILED TO PROVE', verbosity=0)
        v_print(f'Z3 returned {result}', verbosity=0)
