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


# Logical keywords
logical_keywords = ['implies', 'forall', 'exists']


# Dictionaries used for mapping of types and operators
basic_types_mapping = {'int': z3.Int, 'bool': z3.Bool}
array_types_mapping = {'int': z3.IntSort, 'bool': z3.BoolSort}
operators_mapping = {'!': (lambda op: z3.Not(op)), '||': (lambda op1, op2: z3.Or(op1, op2)),
                     '&&': (lambda op1, op2: z3.And(op1, op2)), '+': operator.add, '-': operator.sub, '*': operator.mul,
                     '/': operator.truediv, '%': operator.mod, '^': operator.xor, '<': operator.lt, '<=': operator.le,
                     '==': operator.eq, '!=': operator.ne, '>=': operator.ge, '>': operator.gt}


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
    parser.add_argument('-json_file', required=True, help='The name of the JSON file to get an AST from')
    parser.add_argument('-function_name', required=True, help='Name of the function that should be verified')
    return parser.parse_args(sys.argv[1:])


def filter_dictionary(dictionary, filter_keys):
    """
    Filters the received dictionary according to the received keys - the items that their keys appear in "filter_keys"
    will be removed from the "dictionary"
    :param dictionary: Dictionary to filter
    :param filter_keys: Keys to remove from the dictionary
    :return: None
    """
    for key in filter_keys:
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
            if value != 'True':
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
    print('')
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
    assert q2 is not None
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
    # TODO: Try to split this function
    if expression['type'] == 'CONSTANT':
        # Received expression is a number
        return int(expression['text'])

    elif expression['type'] == 'IDENTIFIER':
        # Received expression is a variable name
        item_text = expression['text']
        if allow_not_defined_variables and (item_text not in variables_dictionary.keys()):
            variables_dictionary[item_text] = z3.Int(item_text)
            logical_variables[item_text] = z3.Int(item_text)
        item_z3_object = variables_dictionary[item_text]
        if variables_mapping and item_z3_object in variables_mapping:
            return variables_mapping[item_z3_object]
        else:
            return item_z3_object

    elif expression['type'] == 'postfix_expression' and expression['children'][1]['text'] == '[':
        assert expression['children'][3]['text'] == ']'
        # Received expression represents access to some array
        items = expression['children']
        array_name = items[0]['text']
        # Doesn't pass "is_destination" or "place_for_index", because they are not relevant inside of the recursion
        array_index = convert_expression_to_z3(variables_dictionary, items[2], variables_mapping,
                                               allow_not_defined_variables=allow_not_defined_variables,
                                               logical_variables=logical_variables)
        array_object = variables_dictionary[array_name]
        if is_destination:
            result = array_object
            place_for_index += [array_index, items[2]]
        else:
            if variables_mapping and array_object in variables_mapping:
                result = get_chain_deepest_mapping(variables_mapping, array_object)[array_index]
            else:
                result = array_object[array_index]
        return result

    elif expression['type'] == 'postfix_expression' and expression['children'][1]['text'] == '(':
        assert expression['children'][3]['text'] == ')'
        keyword = expression['children'][0]['text']
        assert keyword in logical_keywords
        arguments = get_item_by_type(expression['children'], ['argument_expression_list'],
                                     check_uniqueness=True)[0]['children']
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

    elif expression['type'] == 'primary_expression':
        # Received expression is wrapped by brackets
        expression_inside_brackets =\
            convert_expression_to_z3(variables_dictionary, expression['children'][1], variables_mapping, is_destination,
                                     place_for_index, allow_not_defined_variables, logical_variables)
        return expression_inside_brackets

    elif expression['type'] == 'unary_expression':
        operand = convert_expression_to_z3(variables_dictionary, expression['children'][1], variables_mapping,
                                           allow_not_defined_variables=allow_not_defined_variables,
                                           logical_variables=logical_variables)
        expression_operator = expression['children'][0]['text']
        if expression_operator == '-':
            return -operand
        else:
            assert expression_operator == '!'
            return operators_mapping[expression_operator](operand)

    else:
        # Received expression represents some binary operation
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


def prove(formula):
    """
    Checks if the given formula is a tautology, using z3.
    If the formula is a tautology, will print "PROVED",
    Otherwise will print "FAILED TO PROVE. ASSIGNMENT:" with the assignment (counter-example)
    :param formula: z3 formula object
    :return: True if the formula was successfully proved, False otherwise
    """
    solver = z3.Solver()
    solver.push()
    solver.add(z3.Not(formula))
    if solver.check() == z3.unsat:
        print('PROVED')
        result = True
    else:
        print('FAILED TO PROVE. ASSIGNMENT:')
        model = solver.model()
        for declaration in model.decls():
            print(f'{declaration.name()} = {model[declaration]}')
        result = False
    solver.pop()
    return result
