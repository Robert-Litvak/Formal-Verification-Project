import os
import sys
import subprocess
from configparser import ConfigParser
from utils import verbosity_levels


if __name__ == '__main__':
    verifier_configurations = []
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
        for verbosity_level in verbosity_levels:
            output_file_name = os.path.join('output', os.path.basename(configuration['json']).split('.')[0] + '_' +
                                            configuration['function'] + '_verbosity_' + str(verbosity_level) + '.txt')
            current_python = os.path.relpath(sys.executable)
            current_main = os.path.relpath('main.py')
            command = [current_python, current_main, '-j', configuration['json'], '-f', configuration['function'],
                       '-v', str(verbosity_level)]
            if verbosity_level == 0:
                command.append('-d')
            with open(output_file_name, 'w') as output_file:
                process = subprocess.Popen(command, stdout=output_file)
                process.wait()
            print(f'Finished another run. See the results in: {output_file_name}')
