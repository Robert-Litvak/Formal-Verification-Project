import os
from configparser import ConfigParser
import utils
from verifier import Verifier


if __name__ == '__main__':
    args = utils.parse_arguments()
    utils.set_verbosity(args.verbosity)

    verifier_configurations = []
    if args.json_file and args.function_name:
        verifier_configurations = [{'json': args.json_file, 'function': args.function_name}]
    else:
        ini_files = list(map(lambda ini: os.path.join('benchmarks', 'config_files', ini),
                             os.listdir(os.path.join('benchmarks', 'config_files'))))
        for ini_file in ini_files:
            ini_file_basename = os.path.basename(ini_file)
            json_file = os.path.join('benchmarks', 'json', ini_file_basename.split('.ini')[0] + '.c.ast.json')
            parser = ConfigParser()
            parser.read(ini_file)
            for section_name in parser.sections():
                verifier_configurations.append({'json': json_file, 'function': section_name})

    for configuration in verifier_configurations:
        utils.v_print('*' * 113, verbosity=0)
        verifier = Verifier(configuration['json'], configuration['function'])
        if args.paths:
            verifier.verify_paths()
        else:
            verifier.verify_program()
        utils.v_print('\n\n', verbosity=0)
