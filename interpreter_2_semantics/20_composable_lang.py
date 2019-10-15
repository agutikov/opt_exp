
from typing import List, Dict, Tuple, Callable, Any
import lark
from pprint import pprint
from inspect import signature, Parameter
import time
import random
import functools
from enum import Enum
from collections import namedtuple
from copy import deepcopy

# :) id - main function of all functions
_id = lambda x: x

def value_closure(value):
    return lambda *xs: value

# lang -> (grammar -> parser, compiler, interpreter, generator)
# lang: [op],
#   op: "name", "sign", arity, function, grammar_rules
#     grammar_rules: priority, grammar_order, grammar_accociativity, grammar_parantheses
#       priority: non-negative number, root element has min priority
#       grammar_order: infix, prefix, postfix
#       grammar_accociativity: left, right
#       grammar_parantheses: required, available, restricted
#
# For example function call, like f(x) is prefix with parantheses required with accociativity not applicable.
# 
# Compose languages by matching terminal and root nodes of grammar and shifting priority
# Compose predefined languages, like:
#   MYLANG = LOGIC on COMPARE on ARYTHMETIC on (What goes here? Vars and numbers. How to make function with arg, like (_ + 3))
# Compose one language over multiple langs, like:
#   MYLANG = LOGIC on (COMPARE on ARYTHMETIC on (ENV_VARS and NUMBERS) and TYPE_PREDICATES)
#
# Composition of languages and types (signatures) of functions, Category Theory graph for that functions and types.
#
# Ops dict is complete definition of lang grammar and of operational semantics.
#
# Let's think about semantics of functions themself.
# For every function we can define true statements using args and return value and other operations.
# Example: If z == x + y then z > x and z > y and z - x == y and z - y == x.
# Definition of function: if z is the result of add(x, y) then z == x + y.
# Definition of multiplication with addition, foldl and repeat:
#   z == x * y => z == foldl (+) [repeat x times y]
# Also can add other axioms, or properties of operations, like transitivity:
#   transitivity of <: x < y and y < z => x < z
#   transitivity of any op: x op y and y op z => x op z
# So having all this properties with every op compiler can infer properties of composed functions.
# Or if can answer questions like: if (many equations) then if (one equation) is true?
# Anyway what is the meaning of understanding of function semantics?
# It is ability to predict result of function, and explain properties of result.
#

def compile_tree(ops, tree):
    op_name = tree.data if isinstance(tree, lark.Tree) else tree
    return ops[op_name](ops, tree)


def compile_func_call(func, compile_arg, ops, tree):
    """
        Returns lambda that call func from results of compiled functions of tree.children
    """
    sig = signature(func)

    #TODO: 2 types of leafs (Token) handling:
    # 1-st - find it in ops and return function directly
    # 2-nd - compile function from token value, like get var value or return number
    if isinstance(tree, lark.Token):
        return func
    
    # tree without children is Token
    # dirty hack ?
    if len(tree.children) == 0:
        return func

    arity = len(sig.parameters)
    check_arity = True
    if arity >= 1:
        if list(sig.parameters.values())[-1].kind == Parameter.VAR_POSITIONAL:
            check_arity = False

    if check_arity and arity != len(tree.children):
        raise Exception(f'ERROR: compile_func_call: function "{tree.data}" reqires {arity} arguments, provided {len(tree.children)}')

    arg_funcs = [compile_arg(ops, arg) for arg in tree.children]

    if func == _id:
        # optimization :)
        return arg_funcs[0]

    if sig.return_annotation == Callable:
        # Functor
        return func(*arg_funcs)

    return (lambda f, funcs: lambda *xs: f(*(g(*xs) for g in funcs)))(func, arg_funcs)


def generate_compiler_ops(ops_table: Dict[str, Callable]):
    """
        Generates functions that will be called from compile_tree() for compilation of tree nodes.
    """
    ops = {}
    for name, value in ops_table.items():
        if callable(value[0]):
            func = value[0]
        else:
            func = lambda *xs: func

        if value[1] is not None:
            compile_arg = value[1]
        else:
            compile_arg = compile_tree
    
        ops[name] = (lambda f, c_arg: lambda ops, tree: compile_func_call(f, c_arg, ops, tree))(func, compile_arg)
    return ops


def compile(compiler, text):
    compile_ops, parser = compiler
    tree = parser.parse(text)
    print(tree.pretty())
    return compile_tree(compile_ops, tree)


#
# ====================================================================================================
# 
# ====================================================================================================
#


class SyntacticOrder(Enum):
    NOT_APPLICABLE = None
    PREFIX = -1
    INFIX = 0
    POSTFIX = 1

class SyntacticAssociativity(Enum):
    NOT_APPLICABLE = None
    LEFT = -1
    NOT_ASSOCIATIVE = 0,
    RIGHT = 1

class SyntacticParantheses(Enum):
    NOT_APPLICABLE = None
    REQUIRED = True

#TODO: Auto arity

SyntacticDescriptor = namedtuple('SyntacticDescriptor', ['token', 'priority', 'order', 'associativity', 'parantheses'], defaults=[
    0,
    SyntacticOrder.NOT_APPLICABLE,
    SyntacticAssociativity.NOT_APPLICABLE,
    SyntacticParantheses.NOT_APPLICABLE
])

LangOp = namedtuple('LangOp', ['arity', 'syntax', 'op', 'compile_token'], defaults=[_id, None])


def isnamedtupleinstance(x):
    t = type(x)
    b = t.__bases__
    if len(b) != 1 or b[0] != tuple: return False
    f = getattr(t, '_fields', None)
    if not isinstance(f, tuple): return False
    return all(type(n)==str for n in f)

def namedtuple2dict(nt):
    d = {}
    for k, v in nt._asdict().items():
        if isnamedtupleinstance(v):
            d[k] = namedtuple2dict(v)
        elif isinstance(v, Enum):
            d[k] = v.name
        else:
            d[k] = v
    return d

def ops2dict(ops):
    d = {}
    for k, v in ops.items():
        d[k] = namedtuple2dict(v)
    return d



#
# ====================================================================================================
# 
# ====================================================================================================
#

def merge_ops(outer, inner, priority_shift=True):
    i_max_prio = max([op.syntax.priority for op in inner.values()])
    if priority_shift:
        return {**inner, **{k:v._replace(syntax=v.syntax._replace(priority=v.syntax.priority + i_max_prio + 1)) for k,v in outer.items()}}
    else:
        return {**inner, **outer}


def merge_ops_tree(ops_tree):
    """
        Meaning of firt ops tree in list is like in Lisp:
        [X, Y, Z] - X on (Y and Z) - Y and Z have the same priority, X has lower priority
        [X, [Y, Z]] - X on Y on Z - Z has the highest priority, Y has lower priority than Z, X has the lowest priority
    """
    if not isinstance(ops_tree, list):
        return ops_tree
    head = ops_tree[0]
    tail = ops_tree[1:]
    if isinstance(head, list):
        head = merge_ops_tree(head)
    t = {}
    for opst in tail:
        # merge ops trees from tail into one ops dict
        if isinstance(opst, list):
            t = merge_ops(t, merge_ops_tree(opst), priority_shift=False)
        else:
            t = merge_ops(t, opst, priority_shift=False)
    # merge head ops ontop tail ops
    return merge_ops(head, t)




grammar_footer = """
%import common.CNAME
%import common.NUMBER

%import common.WS_INLINE
%import common.NEWLINE
%ignore WS_INLINE
%ignore NEWLINE
"""

def group_ops_prio(ops):
    d = {}
    for k, v in ops.items():
        if v.syntax.priority not in d:
            d[v.syntax.priority] = {}
        d[v.syntax.priority][k] = v
    return d


def generate_grammar_rule(ops, inner_rule_name, rule_name):
    # every op produce a match for non-terminal 
    # op key used as alias
    matches = []

    if inner_rule_name is not None:
        matches.append(([inner_rule_name], None))

    for op_name, op in ops.items():
        if op.arity == 0:
            if '|' in op.syntax.token:
                match = [f'( {op.syntax.token} )']
            else:
                match = [op.syntax.token]
        else:
            #TODO: Multi-arity
            #TODO: Parantheses of function args
            token = f'"{op.syntax.token}"'
            if op.arity == 2 and op.syntax.order == SyntacticOrder.INFIX:
                if op.syntax.associativity == SyntacticAssociativity.RIGHT:
                    match = [inner_rule_name, token, rule_name]
                elif op.syntax.associativity == SyntacticAssociativity.LEFT:
                    match = [rule_name, token, inner_rule_name]
                elif op.syntax.associativity == SyntacticAssociativity.NOT_ASSOCIATIVE:
                    match = [inner_rule_name, token, inner_rule_name]
                else:
                    raise Exception(f'ERROR: generate_grammar_rule: invalid "{op_name}" in {ops2dict(ops)}')
            else:
                if op.syntax.order == SyntacticOrder.INFIX:
                    raise Exception(f'ERROR: generate_grammar_rule: invalid "{op_name}" in {ops2dict(ops)}')

                #TODO: When use inner rule name and one this rule name?
                if op.syntax.order == SyntacticOrder.PREFIX:
                    match = [token] + [inner_rule_name]*op.arity
                elif op.syntax.order == SyntacticOrder.POSTFIX:
                    match = [inner_rule_name]*op.arity + [token]
                else:
                    raise Exception(f'ERROR: generate_grammar_rule: invalid "{op_name}" in {ops2dict(ops)}')
        matches.append((match, op_name))

    return matches


def generate_grammar(ops):
    rules = {} # rule name -> list of pairs (item match: list of terminals and non-terminals, optional alias)

    ops_by_prio = group_ops_prio(ops)
    inner_rule_name = None
    for prio in sorted(ops_by_prio):
        # every priority produce a grammar rule
        # e.g. ops of same priority compose one grammar rule
        rule_name = f'rule_{prio}'
        rules[rule_name] = generate_grammar_rule(ops_by_prio[prio], inner_rule_name, rule_name)
        inner_rule_name = rule_name

    rules['rule_0'].append(([f'"(" {rule_name} ")"'], None))

    grammar = grammar_footer
    for rule_name, rule in rules.items():
        rule_str = '\n  | '.join([' '.join(match) + (' -> ' + alias if alias is not None else '') for match, alias in rule])
        grammar = "?" + rule_name + ": " + rule_str + "\n\n" + grammar

    return '\n' + grammar, rule_name


def get_plain_ops(ops):
    return {k : (v.op, v.compile_token) for k, v in ops.items()}


def make_compiler(ops_tree):
    ops = merge_ops_tree(ops_tree)

    grammar, start_symbol = generate_grammar(ops)
    print(grammar)
    parser = lark.Lark(grammar, start=start_symbol)

    cops = generate_compiler_ops(get_plain_ops(ops))

    return (cops, parser)


#
# ====================================================================================================
# 
# ====================================================================================================
#


logic_literals = {
    "false": LangOp(
        arity=0,
        op=False,
        syntax=SyntacticDescriptor('"False" | "FALSE" | "false" | "F" | "f"')),
    
    "true": LangOp(
        arity=0,
        op=True,
        syntax=SyntacticDescriptor('"True" | "TRUE" | "true" | "T" | "t"')),
}


def compile_const(_, token):
    return (lambda const_name: lambda x: x[const_name])(token) 

constants = {
    "constant": LangOp(
        arity=0,
        compile_token=compile_const,
        syntax=SyntacticDescriptor('CNAME')),
}

logic = {
    "or": LangOp(
        arity=2,
        op=lambda x, y: x or y,
        syntax=SyntacticDescriptor(
            token="or",
            priority=2,
            order=SyntacticOrder.INFIX,
            associativity=SyntacticAssociativity.LEFT,
            parantheses=SyntacticParantheses.NOT_APPLICABLE
        )
    ),

    "and": LangOp(
        arity=2,
        op=lambda x, y: x and y,
        syntax=SyntacticDescriptor(
            token="and",
            priority=1,
            order=SyntacticOrder.INFIX,
            associativity=SyntacticAssociativity.LEFT,
            parantheses=SyntacticParantheses.NOT_APPLICABLE
        )
    ),

    "not": LangOp(
        arity=1,
        op=lambda x: not x,
        syntax=SyntacticDescriptor(
            token="not",
            priority=0,
            order=SyntacticOrder.PREFIX,
            associativity=SyntacticAssociativity.RIGHT,
            parantheses=SyntacticParantheses.NOT_APPLICABLE
        )
    ),
}


# it works because constant_ops goes before logic_literals_ops
# if not - parser will consider "False" and other literals as CNAME
c1 = make_compiler([logic, constants, logic_literals])

f = compile(c1, 'x and y or not z or F')

print(f({'x': True, 'y': False, 'z': False}))



#
# ====================================================================================================
# 
# ====================================================================================================
#


numbers = {
    "number": LangOp(
        arity=0,
        compile_token=lambda _, token: value_closure(float(token)),
        syntax=SyntacticDescriptor('NUMBER'))
}

arithmetic = {
    "sub": LangOp(
        arity=2,
        op=lambda x, y: x - y,
        syntax=SyntacticDescriptor(
            token="-",
            priority=3,
            order=SyntacticOrder.INFIX,
            associativity=SyntacticAssociativity.LEFT,
            parantheses=SyntacticParantheses.NOT_APPLICABLE
        )
    ),

    "add": LangOp(
        arity=2,
        op=lambda x, y: x + y,
        syntax=SyntacticDescriptor(
            token="+",
            priority=3,
            order=SyntacticOrder.INFIX,
            associativity=SyntacticAssociativity.LEFT,
            parantheses=SyntacticParantheses.NOT_APPLICABLE
        )
    ),

    "div": LangOp(
        arity=2,
        op=lambda x, y: x / y,
        syntax=SyntacticDescriptor(
            token="/",
            priority=2,
            order=SyntacticOrder.INFIX,
            associativity=SyntacticAssociativity.LEFT,
            parantheses=SyntacticParantheses.NOT_APPLICABLE
        )
    ),

    "mul": LangOp(
        arity=2,
        op=lambda x, y: x * y,
        syntax=SyntacticDescriptor(
            token="*",
            priority=2,
            order=SyntacticOrder.INFIX,
            associativity=SyntacticAssociativity.LEFT,
            parantheses=SyntacticParantheses.NOT_APPLICABLE
        )
    ),
    
    "neg": LangOp(
        arity=1,
        op=lambda x: -x,
        syntax=SyntacticDescriptor(
            token="-",
            priority=1,
            order=SyntacticOrder.PREFIX,
            associativity=SyntacticAssociativity.RIGHT,
            parantheses=SyntacticParantheses.NOT_APPLICABLE
        )
    ),
    
    "pow": LangOp(
        arity=2,
        op=lambda x, y: x ** y,
        syntax=SyntacticDescriptor(
            token="^",
            priority=0,
            order=SyntacticOrder.INFIX,
            associativity=SyntacticAssociativity.RIGHT,
            parantheses=SyntacticParantheses.NOT_APPLICABLE
        )
    ),
}


comparison = {
    "eq": LangOp(
        arity=2,
        op=lambda x, y: x == y,
        syntax=SyntacticDescriptor(
            token="==",
            priority=0,
            order=SyntacticOrder.INFIX,
            associativity=SyntacticAssociativity.NOT_ASSOCIATIVE,
            parantheses=SyntacticParantheses.NOT_APPLICABLE
        )
    ),

    "neq": LangOp(
        arity=2,
        op=lambda x, y: x != y,
        syntax=SyntacticDescriptor(
            token="!=",
            priority=0,
            order=SyntacticOrder.INFIX,
            associativity=SyntacticAssociativity.NOT_ASSOCIATIVE,
            parantheses=SyntacticParantheses.NOT_APPLICABLE
        )
    ),

    "gt": LangOp(
        arity=2,
        op=lambda x, y: x > y,
        syntax=SyntacticDescriptor(
            token=">",
            priority=0,
            order=SyntacticOrder.INFIX,
            associativity=SyntacticAssociativity.NOT_ASSOCIATIVE,
            parantheses=SyntacticParantheses.NOT_APPLICABLE
        )
    ),

    "gte": LangOp(
        arity=2,
        op=lambda x, y: x >= y,
        syntax=SyntacticDescriptor(
            token=">=",
            priority=0,
            order=SyntacticOrder.INFIX,
            associativity=SyntacticAssociativity.NOT_ASSOCIATIVE,
            parantheses=SyntacticParantheses.NOT_APPLICABLE
        )
    ),

    "lt": LangOp(
        arity=2,
        op=lambda x, y: x < y,
        syntax=SyntacticDescriptor(
            token="<",
            priority=0,
            order=SyntacticOrder.INFIX,
            associativity=SyntacticAssociativity.NOT_ASSOCIATIVE,
            parantheses=SyntacticParantheses.NOT_APPLICABLE
        )
    ),

    "lte": LangOp(
        arity=2,
        op=lambda x, y: x <= y,
        syntax=SyntacticDescriptor(
            token="<=",
            priority=0,
            order=SyntacticOrder.INFIX,
            associativity=SyntacticAssociativity.NOT_ASSOCIATIVE,
            parantheses=SyntacticParantheses.NOT_APPLICABLE
        )
    ),
}


c2 = make_compiler([logic, [comparison, [arithmetic, numbers, constants]]])

text = "f * g + e > d and a < b and (a == b or a * c >= b ^ 2)"
env = {'a': 100, 'b': 200, 'c': 3, 'd': 9768, 'e': 2334, 'g': -1, 'f': -5.5}

f = compile(c2, text)

print(f(env))

