from cfg import CFG
from path_finder import PathFinder


class Verifier:
    def __init__(self, json_file, function_name):
        self.json_file = json_file
        self.function_name = function_name
        self.cfg = CFG(self.json_file, self.function_name)

    def __call__(self):
        self.cfg.create_cfg()
        path_finder = PathFinder(self.cfg)
        path_finder.generate_paths()
        paths = path_finder.paths
        self.cfg.invariants_back_patch(paths)

        print(f'Found {len(paths)} paths:')
        for path in paths:
            path.print_path()
        self.cfg.print_variables()

        not_proved_paths = list(filter(lambda cfg_path: not cfg_path.path_proved, paths))
        if not not_proved_paths:
            print('PROGRAM IS SUCCESSFULLY PROVED')
        else:
            print('FAILED TO PROVE THE PROGRAM. SEE THE FOLLOWING PATHS:')
            for path in not_proved_paths:
                print(f'Path begin at: {path.start_node}')
                print(f'Path ends at {path.end_node}')
                print(f'Path action items are {path.action_items}')
