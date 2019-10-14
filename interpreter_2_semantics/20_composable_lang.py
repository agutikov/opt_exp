
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

#TODO: lang -> (grammar -> parser, compiler, interpreter, generator)
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
#   MYLANG = LOGIC on (COMPARE on ARYTHMETIC on (ENV_VARS, NUMBERS), TYPE_PREDICATES)
#
# Composition of languages and types (signatures) of functions, Category Theory graph for that functions and types.
#
# Ops dict is complete definition of lang grammar and of operational semantics.
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
        if callable(value):
            func = value
            compile_arg = compile_tree
        else: 
            # value is tuple
            func = value[0]
            compile_arg = value[1]
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
    RIGHT = 1

class SyntacticParantheses(Enum):
    NOT_APPLICABLE = None
    REQUIRED = True

SyntacticDescriptor = namedtuple('SyntacticDescriptor', ['token', 'priority', 'order', 'associativity', 'parantheses'])
def LiteralSyntacticDescriptor(token):
    return SyntacticDescriptor(token, 0,
                               SyntacticOrder.NOT_APPLICABLE,
                               SyntacticAssociativity.NOT_APPLICABLE,
                               SyntacticParantheses.NOT_APPLICABLE)

LangOp = namedtuple('LangOp', ['arity', 'op', 'compile_token', 'syntax'])


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

def merge_ops(inner, outer, priority_shift=True):
    i_max_prio = max([op.syntax.priority for op in inner.values()])
    if priority_shift:
        return {**inner, **{k:v._replace(syntax=v.syntax._replace(priority=v.syntax.priority + i_max_prio + 1)) for k,v in outer.items()}}
    else:
        return {**inner, **outer}



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
            #TODO: Parantheses for eval ordering
            token = f'"{op.syntax.token}"'
            if op.arity == 2 and op.syntax.order == SyntacticOrder.INFIX:
                if op.syntax.associativity == SyntacticAssociativity.RIGHT:
                    match = [inner_rule_name, token, rule_name]
                elif op.syntax.associativity == SyntacticAssociativity.LEFT:
                    match = [rule_name, token, inner_rule_name]
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

    grammar = grammar_footer
    for rule_name, rule in rules.items():
        rule_str = '\n  | '.join([' '.join(match) + (' -> ' + alias if alias is not None else '') for match, alias in rule])
        grammar = "?" + rule_name + ": " + rule_str + "\n\n" + grammar

    return '\n' + grammar, rule_name


def get_plain_ops(ops):
    return {k : v.op if v.compile_token is None else (v.op, v.compile_token) for k, v in ops.items()}


#
# ====================================================================================================
# 
# ====================================================================================================
#


logic_literal_ops = {
    "logic_literal": LangOp(
        arity=0,
        op=_id,
        compile_token=lambda _, token: value_closure(bool(token)),
        syntax=LiteralSyntacticDescriptor('"True" | "False"'))
}

logic_literals_ops = {
    "false": LangOp(
        arity=0,
        op=lambda : False,
        compile_token=None,
        syntax=LiteralSyntacticDescriptor('"False" | "FALSE" | "false" | "F" | "f"')),
    
    "true": LangOp(
        arity=0,
        op=lambda : True,
        compile_token=None,
        syntax=LiteralSyntacticDescriptor('"True" | "TRUE" | "true" | "T" | "t"')),
}


def compile_const(_, token):
    return (lambda const_name: lambda x: x[const_name])(token) 

constant_ops = {
    "constant": LangOp(
        arity=0,
        op=_id,
        compile_token=compile_const,
        syntax=LiteralSyntacticDescriptor('CNAME')),
}

logic_ops_lang = {
    "or": LangOp(
        arity=2,
        op=lambda x, y: x or y,
        compile_token=None,
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
        compile_token=None,
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
        compile_token=None,
        syntax=SyntacticDescriptor(
            token="not",
            priority=0,
            order=SyntacticOrder.PREFIX,
            associativity=SyntacticAssociativity.RIGHT,
            parantheses=SyntacticParantheses.NOT_APPLICABLE
        )
    ),
}


ops2 = merge_ops(logic_literals_ops, constant_ops, priority_shift=False)
ops3 = merge_ops(ops2, logic_ops_lang)

g, start_symbol = generate_grammar(ops3)
print(start_symbol)
print(g)


cops = generate_compiler_ops(get_plain_ops(ops3))

parser = lark.Lark(g, start=start_symbol)

compiler = (cops, parser)

f = compile(compiler, 'x and y or not z')

print(f({'x': True, 'y': False, 'z': False}))



