import utils
from cfg import CFG
from cfg_paths import CfgPaths


def main():
    """
    The main function of the program
    :return: None
    """
    args = utils.parse_arguments()
    cfg = CFG(args.json_file, args.function_name)
    cfg.create_cfg()
    paths = CfgPaths(cfg)
    paths.generate_paths()
    paths.invariants_back_patch()
    paths.print_paths()
    cfg.print_variables()
    if not paths.not_proved_paths:
        print('PROGRAM IS SUCCESSFULLY PROVED')
    else:
        print('FAILED TO PROVE THE PROGRAM. SEE THE FOLLOWING PATHS:')
        for first, last, path in paths.not_proved_paths:
            print(f'Path begin at: {first}')
            print(f'Path ends at {last}')
            print(f'Path action items are {path}')


if __name__ == '__main__':
    main()
