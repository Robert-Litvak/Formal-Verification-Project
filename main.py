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
        need_to_verify = True
        while need_to_verify:
            verifier = Verifier(configuration['json'], configuration['function'])
            if args.paths:
                verifier.verify_paths()
                need_to_verify = False
            elif args.manual_horn_clauses:
                verification_succeeded = verifier.verify_program()
                need_to_verify = not verification_succeeded
                if need_to_verify:
                    args.manual_horn_clauses = False
                    args.paths = True
            else:
                verification_succeeded = verifier.verify_program_fixed_point()
                need_to_verify = not verification_succeeded
                if need_to_verify:
                    args.manual_horn_clauses = True
        utils.v_print('', verbosity=0)
