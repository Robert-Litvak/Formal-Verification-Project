from cfg_nodes import StartNode
from cfg_nodes import HaltNode
from cfg_nodes import ConditionNode
from cfg_nodes import AssignmentNode
from cfg_nodes import AssertNode
from path import Path


class PathFinder:
    """Class for finding paths in CFG"""
    def __init__(self, cfg):
        self.cfg = cfg
        self.paths = []
        self.stack = []
        self.cut_points = []
        self.cut_points_queue = [(self.cfg.start, None)]

    def recursive_paths(self, sub_cfg, path_root):
        """
        Searches recursively for paths to the next cut points
        :param sub_cfg: CFG node to start searching from it (it is the second node of each path that will be found)
        :param path_root: First node of each path that will be found
        :return: None
        """
        # If node is a cut point, we'll check whether it was added into the list and if no - add it and finish the path
        if sub_cfg.is_cut_point:
            # Another path is found - store the first node of the path, and the action items that represent the path
            discovered_path = Path(path_root, sub_cfg, self.stack.copy(), self.cfg.variables)
            self.paths.append(discovered_path)
            if sub_cfg not in self.cut_points:
                self.cut_points.append(sub_cfg)
                if isinstance(sub_cfg, ConditionNode):
                    self.cut_points_queue += [(sub_cfg, 'T'), (sub_cfg, 'F')]
                elif isinstance(sub_cfg, AssertNode):
                    self.cut_points_queue += [(sub_cfg, 'M')]
                else:
                    assert isinstance(sub_cfg, HaltNode)
            return
        # If node is an assignment, just keep going with the path
        if isinstance(sub_cfg, AssignmentNode):
            self.stack.append(None)
            self.recursive_paths(sub_cfg.son, path_root)
            self.stack.pop()
        # If node is a condition, generate 2 paths from here: one true and one false
        elif isinstance(sub_cfg, ConditionNode) and not sub_cfg.is_cut_point:
            self.stack.append(False)
            self.recursive_paths(sub_cfg.son_false, path_root)
            self.stack.pop()
            self.stack.append(True)
            self.recursive_paths(sub_cfg.son_true, path_root)
            self.stack.pop()

    def find_paths_to_the_next_cut_points(self, path_root, direction):
        """
        Finds basic paths to all the closest next cut points
        :param path_root: CFG node to start searching from it
        :param direction: The direction to use from the first node of the path
        :return: None
        """
        # Assumption, that start node can be only at the start of the path
        if isinstance(path_root, StartNode):
            self.stack.append(None)
            self.recursive_paths(path_root.son, path_root)
            self.stack.pop()
        elif direction is not None:
            assert direction in ['T', 'F', 'M']
            # Direction T means that we current node is condition node (usually while or for)
            # and we choose path where condition is satisfied
            if direction == 'T':
                self.stack.append(True)
                self.recursive_paths(path_root.son_true, path_root)
                self.stack.pop()
            # Direction F means that we current node is condition node
            # and we choose path where condition is not satisfied
            elif direction == 'F':
                self.stack.append(False)
                self.recursive_paths(path_root.son_false, path_root)
                self.stack.pop()
            # Direction M means that we current node is not a condition node (usually assert)
            else:
                # direction == 'M'
                self.stack.append(None)
                self.recursive_paths(path_root.son, path_root)
                self.stack.pop()

    def generate_paths(self):
        """
        Finds all the basic paths of the program. The paths will be stored in self.paths
        :return: None
        """
        # Wrapper for path search algorithm. Here we start BFS search for cut points.
        # While set is not empty, we will take out cut point and generate paths from it. If on a path way we will find
        # cut point that wasn't fond yet, we will add it to the set.
        while self.cut_points_queue:
            current_cut_point = self.cut_points_queue[0]
            self.cut_points_queue.remove(current_cut_point)
            self.find_paths_to_the_next_cut_points(path_root=current_cut_point[0], direction=current_cut_point[1])
