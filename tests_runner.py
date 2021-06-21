import os
import re
import sys
import subprocess
from configparser import ConfigParser


def verify_all_available_functions():
    run_options_list = []
    ini_files = list(map(lambda ini: os.path.join('benchmarks', 'config_files', ini),
                         os.listdir(os.path.join('benchmarks', 'config_files'))))
    for ini_file in ini_files:
        ini_file_basename = os.path.basename(ini_file)
        json_file = os.path.join('benchmarks', 'json', ini_file_basename.split('.ini')[0] + '.c.ast.json')
        parser = ConfigParser()
        parser.read(ini_file)
        for section_name in parser.sections():
            run_options_list.append({'-j': json_file, '-f': section_name})

    with open('tests_output.txt', 'w') as output_file:
        for flags in run_options_list:
            command = [sys.executable, 'main.py', '-j', flags['-j'], '-f', flags['-f']]
            output_file.write('*' * 113 + '\n')
            output_file.write(f'Executing command: {" ".join(command)}\n')
            process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            try:
                stdout, stderr = process.communicate(timeout=5)
                process.wait(timeout=5)
                if stdout:
                    stdout_str = re.sub(r'\n', '', stdout.decode(sys.stdout.encoding))
                    output_file.write(stdout_str)
                if stderr:
                    stderr_str = re.sub(r'\n', '', stdout.decode(sys.stderr.encoding))
                    output_file.write(stderr_str)
            except subprocess.TimeoutExpired:
                process.kill()
                output_file.write('Verifier did not response for more than 5 seconds. ' +
                                  'The process was killed.\nFAILED TO PROVE')
            output_file.write('\n' * 5)


if __name__ == '__main__':
    verify_all_available_functions()
