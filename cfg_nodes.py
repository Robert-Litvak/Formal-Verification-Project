# Classes to represent the CFG nodes
class StartNode:
    """Class representing CFG start node"""
    def __init__(self, son):
        self.son = son
        self.is_cut_point = True
        self.invariant = None
    
    def __str__(self):
        return '***START***'


class HaltNode:
    """Class representing CFG halt node"""
    def __init__(self):
        self.is_cut_point = True
        self.invariant = None
    
    def __str__(self):
        return '***HALT***'


class AssignmentNode:
    """Class representing CFG assignment node"""
    def __init__(self, son, expression_subtree, expression_z3, target_z3, target_index_subtree=None,
                 target_index_z3=None):
        self.son = son
        self.expression_subtree = expression_subtree
        self.target_index_subtree = target_index_subtree
        self.target_z3 = target_z3
        self.expression_z3 = expression_z3
        self.target_index_z3 = target_index_z3
        self.is_cut_point = False
    
    def __str__(self):
        if self.target_index_z3 is None:
            return f'***ASSIGNMENT***\t{self.target_z3} = {self.expression_z3}'
        else:
            return f'***ASSIGNMENT***\t{self.target_z3}[{self.target_index_z3}] = {self.expression_z3}'


class ConditionNode:
    """Class representing CFG condition node"""
    def __init__(self, true_son, false_son, condition_subtree, condition_z3, is_cut_point=False, start_line=0):
        self.son_true = true_son
        self.son_false = false_son
        self.condition_subtree = condition_subtree
        self.condition_z3 = condition_z3
        self.is_cut_point = is_cut_point
        self.start_line = start_line
        self.invariant = None
        self.spacer_invariant = None

    def __str__(self):
        return f'***CONDITION***\t{self.condition_z3}'


class AssertNode:
    """Class representing special assert nodes in CFG"""
    def __init__(self, son, expression_subtree, expression_z3):
        self.son = son
        self.expression_subtree = expression_subtree
        self.expression_z3 = expression_z3
        self.is_cut_point = True
        self.invariant = expression_z3

    def __str__(self):
        return f'***ASSERT***\t{self.expression_z3}'
