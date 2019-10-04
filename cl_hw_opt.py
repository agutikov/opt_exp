#!/usr/bin/env python3

import uuid
from typing import List, Dict, Tuple, Callable, Any
import lark
from pprint import pprint
from inspect import signature
import time
import random

"""
=====================================================================================================
Units

    Units calculation required for constraints.
    Like byte/s can't be equal to s^-1.
=====================================================================================================
"""




"""
=====================================================================================================
Type Predicates

    One line like "a.b.c" represents category - subset c in subset b in subset a.
        "a.b.c" -> ["a", "b", "c"]

    Category x is a subcategory of category c if x is equal to c or is longer than c and contains c from root.
        "a.b.c" is a subcategory of "a.b"
        "a.b" is a subcategory of "a.b"

    List of categories represent intersection of subsets.
        "a.b.c, x.y.z" -> [["a", "b", "c"], ["x", "y", "z"]]

    Predicate match if any of category in list is a subcategory.
        "a.b.c, x.y.z" is a subcategory of "a.b"

    Logic operations are usual [or, and, not] on match with category.
        "a.b.c, x.y.z" match "a.b and x.y and not x.y.t"
        "a.b.c, x.y.z" not match "a.b.c.d or x.y.z.r or not x.y.z"

=====================================================================================================
"""

def parse_cat(cat: str) -> List[str]:
    return [c.strip() for c in cat.strip().split('.') if len(c.strip()) > 0]

def parse_categories(cats: str) -> List[List[str]]:
    return [parse_cat(c) for c in cats.split(',') if len(c.strip()) > 0]

def serialize_cat(cat: List[str]) -> str:
    return '.'.join(cat)

def serialize_categories(cats: List[List[str]]) -> str:
    return ', '.join([serialize_cat(c) for c in cats])

def is_subcat(c: List[str], sub_c: List[str]) -> bool:
    """
        Return True if sub_c is a subcategory of c.
    """
    # if c is more precize category then sub_c can't be subcategory of c.
    if len(c) > len(sub_c):
        return False

    for c_el, x_el in zip(c, sub_c):
        if c_el != x_el:
            return False
    return True

def cat_contains_subcat_from_list(cat: List[str], sub_cat_list: List[List[str]]) -> bool:
    """
        Return True if any of x is a subcategory of c.
    """
    for sub_c in sub_cat_list:
        if is_subcat(cat, sub_c):
            return True
    return False

#
# ====================================================================================================
# Compile tree into function from one argument with lambdas
# ====================================================================================================
#

#TODO: WTF? How I've get here? Repeat it again and write a writeup. 
#      In Python, C++ and Haskell.
#      Lambda compilation vs interpretation, compare implementation and performance.

#TODO: Generator from grammar, random node selection and random/fixed limited depth.


#TODO: Pack grammar,ops,start_symbol into language and add wrap_language(outer_lang, iner_lang) function

#TODO: lang -> (grammar -> parser, compiler, interpreter, generator)
# lang: [op], 
#   op: "name", "sign", arity, function, grammar_rules
#     grammar_rules: priority, grammar_order, grammar_accociativity, grammar_parantheses
#       priority: non-negative number, root element has min priority
#       grammar_order: infix, prefix, postfix
#       grammar_accociativity: left, right
#       grammar_parantheses: required, available, restricted
#
# Compose languages by matching terminal and root nodes of grammar and shifting priority
# Compose predefined languages like:
#   MYLANG = LOGIC on COMPARE on ARYTHMETIC on (What goes here? Vars and numbers. How to make function with arg, like (_ + 3))



_id = lambda x: x

#TODO: compile_tree and compile_token ???

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

    arity = len(sig.parameters)
    if arity != len(tree.children):
        raise f'ERROR: compile_func_call: function "{tree.data}" reqires {arity} arguments, provided {len(tree.children)}'

    arg_funcs = [compile_arg(ops, arg) for arg in tree.children]

    if func == _id:
        # optimization :)
        return arg_funcs[0]

    if sig.return_annotation == Callable:
        # Functor
        return func(*arg_funcs)

    #TODO: Question - are every g(x) calculated or only required?
    return (lambda f, *funcs: lambda x: f(*(g(x) for g in funcs)))(func, *arg_funcs)


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
    #print(tree.pretty())
    return compile_tree(compile_ops, tree)


#TODO: Linearize calculation of same functions on one level, like pipe composition

#
# ====================================================================================================
# Interpretation
# ====================================================================================================
#

def interpret_tree(ops, env, tree):
    """
        Interpretation works directly with same ops as compilation, without generate_compiler_ops().
    """
    op_name = tree.data if isinstance(tree, lark.Tree) else tree

    value = ops[op_name]

    if callable(value):
        func = value
        interpret_arg = interpret_tree
    else: 
        # value is tuple
        func = value[0]
        interpret_arg = lambda ops, env, tree: value[1](ops, tree)(env)

    if isinstance(tree, lark.Token):
        return func(env)

    sig = signature(func)
    arity = len(sig.parameters)
    if arity != len(tree.children):
        raise f'ERROR: interpret_tree: function "{tree.data}" invalid number of arguments: {len(tree.children)} != {arity}'

    # optimization - eval on demand
    fargs = [(lambda _ops, _tree: lambda x: interpret_arg(_ops, x, _tree))(ops, subtree) for subtree in tree.children]

    if sig.return_annotation == Callable:
        # Functor - pass carried interpret_arg, not results as arguments to functor
        return func(*fargs)(env)
    else:
        #TODO: Question - are every g(x) calculated or only required?
        return (lambda f, fa: lambda e: f(*(g(e) for g in fa)))(func, fargs)(env)


def interpret(interpreter, text, env):
    ops, parser = interpreter
    tree = parser.parse(text)
    #print(tree.pretty())
    return interpret_tree(ops, env, tree)

#
# ====================================================================================================
# Test
# ====================================================================================================
#

class NodeCounter:
    def __init__(self):
        self.node_counter = 0
        self.subtree_counter = 0
        self.leaf_counter = 0
        self.depth = 0
        self.max_depth = 0

    def visit(self, tree):
        self.depth += 1
        if self.max_depth < self.depth:
            self.max_depth = self.depth

        self.node_counter += 1
        if isinstance(tree, lark.Tree):
            self.subtree_counter += 1
            for node in tree.children:
                self.visit(node)
        else:
            self.leaf_counter += 1

        self.depth -= 1

def count_nodes(tree):
    nc = NodeCounter()
    nc.visit(tree)
    return nc.node_counter, nc.subtree_counter, nc.leaf_counter, nc.max_depth
 
def test(ops, parser, text, env, result, verbose=False, debug=False):
    print()
    if verbose:
        print(text)
        print()
        print(env)
    compiler_ops = generate_compiler_ops(ops)

    start = time.process_time()
    tree = parser.parse(text)
    parse_elapsed = time.process_time() - start
    if verbose:
        print()
        print(tree.pretty())

    nodes, subtrees, leafs, max_depth = count_nodes(tree)
    print(f'chars: {len(text)}, nodes: {nodes}, subtrees: {subtrees}, leafs: {leafs}, max_depth: {max_depth}')

    start = time.process_time()
    f = compile_tree(compiler_ops, tree)
    compile_elapsed = time.process_time() - start

    start = time.process_time()
    r = f(env)
    exec_elapsed = time.process_time() - start

    if not debug:
        assert(result == r)

    start = time.process_time()
    r = interpret_tree(ops, env, tree)
    interpret_elapsed = time.process_time() - start

    if not debug:
        assert(result == r)

    print(f"parse: {parse_elapsed}, " 
          f"compile: {compile_elapsed}, "
          f"exec: {exec_elapsed}, "
          f"interpret: {interpret_elapsed}, "
          f"speedup: {interpret_elapsed/exec_elapsed}")

#
# ====================================================================================================
# Logic operations
# ====================================================================================================
#

LOGIC_GRAMMAR = """
?start: dis

?dis: con
  | dis "or" con       -> or

?con: neg
  | con "and" neg      -> and

?neg: item
  | "not" item         -> not

?item: NAME            -> {}
  | "(" dis ")"

NAME: /{}/

%import common.WS
%ignore WS
"""

def get_logic_grammar_parser(name, regex):
   return lark.Lark(LOGIC_GRAMMAR.format(name, regex))

logic_predicate_ops = {
    "or": lambda a, b: a or b,
    "and": lambda a, b: a and b,
    "not": lambda b: not b,
}

#
# ====================================================================================================
# Combine category-subcategory matching and logic operations
# ====================================================================================================
#

# merge grammar
cat_logic_grammar_parser = get_logic_grammar_parser("call", r"([a-zA-Z0-9_]+\.)*[a-zA-Z0-9_]+")

def compile_cat_predicate_terminal_symbol(ops, tree):
    """
        Returns function from x that represent match of x with category, represented by tree.
    """
    return (lambda cap_cat: lambda x: cat_contains_subcat_from_list(cap_cat, x))(parse_cat(tree)) 

cat_ops = {
    "call": (_id, compile_cat_predicate_terminal_symbol)
}

# merge compile_ops
cat_predicate_ops = {
    **logic_predicate_ops,
    **cat_ops
}

cat_predicate_compile_ops = generate_compiler_ops(cat_predicate_ops)

def compile_cat_predicate(p: str):
    return compile((cat_predicate_compile_ops, cat_logic_grammar_parser), p)

def interpret_cat_predicate(p: str, env):
    return interpret((cat_predicate_ops, cat_logic_grammar_parser), p, env)


assert(compile_cat_predicate("a.b")(parse_categories("a.b.c, x.y.z")))
assert(interpret_cat_predicate("a.b", parse_categories("a.b.c, x.y.z")))

assert(compile_cat_predicate("a.b and x.y")(parse_categories("a.b.c, x.y.z")))
assert(interpret_cat_predicate("a.b and x.y", parse_categories("a.b.c, x.y.z")))

c = parse_categories("hw.disk.type.ssd, hw.vendor.intel, hw.disk.func.discard")
p = compile_cat_predicate("hw.disk and not hw.disk.type.nvme or not hw.disk.func.discard and hw.vendor.intel")
assert(p(c))

c = parse_categories("hw.disk.type.nvme, hw.vendor.intel, hw.disk.func.discard")
p = compile_cat_predicate("hw.disk and not (hw.disk.type.nvme or not hw.disk.func.discard) and hw.vendor.intel")
assert(not p(c))

assert(compile_cat_predicate("a.b and not (x.y.f or a.b.z) and not x.y.t")(parse_categories("a.b.c, x.y.z")))
assert(not compile_cat_predicate("a.b.c.d or x.y.z.r or not x.y.z")(parse_categories("a.b.c, x.y.z")))


#
# ====================================================================================================
# Arithmetic functions on environment with variable values.
# ====================================================================================================
#

ARITHMETIC_GRAMMAR = """
?sum: product
  | sum "+" product       -> add
  | sum "-" product       -> sub

?product: power
  | product "*" power     -> mul
  | product "/" power     -> div

?power: value
  | value "**" power      -> pow

?value: NUMBER            -> number
  | NAME                  -> var
  | "-" power             -> neg
  | "(" sum ")"

%import common.CNAME -> NAME
%import common.NUMBER

%import common.WS_INLINE
%import common.NEWLINE
%ignore WS_INLINE
%ignore NEWLINE
"""

arithmetic_parser = lark.Lark(ARITHMETIC_GRAMMAR, start="sum")

# Number is function that returns this number ;)
def compile_number(ops, tree):
    """
        Returns function from x that returns value of number.
    """
    return (lambda N: lambda x: N)(float(tree)) 

def compile_var(ops, tree):
    return (lambda var_name: lambda x: x[var_name])(tree) 

arithmetic_ops = {
    "add": lambda x, y: x + y,
    "sub": lambda x, y: x - y,
    "mul": lambda x, y: x * y,
    "div": lambda x, y: x / y,
    "neg": lambda x: -x,
    "pow": lambda x, y: x ** y,
    "number": (_id, compile_number),
    "var": (_id, compile_var),
}

arithmetic_compile_ops = generate_compiler_ops(arithmetic_ops)

def compile_arithmetic(text: str):
    return compile((arithmetic_compile_ops, arithmetic_parser), text)


assert(0 == compile_arithmetic("0")({}))
assert(-1 == compile_arithmetic("-1")({}))
assert(1.1 == compile_arithmetic("1.1")({}))

test(arithmetic_ops, arithmetic_parser, "x * 2 + -y", {'x': 1, 'y': 2}, 0)
test(arithmetic_ops, arithmetic_parser, "x / 2 - 1 / y", {'x': 1, 'y': 2}, 0)
test(arithmetic_ops, arithmetic_parser, "x ** y - 1", {'x': 1, 'y': 2}, 0)

#
# ====================================================================================================
# Arithmetic predicates on environment with variable values.
# ====================================================================================================
#

# Wrapping languages by concat grammars and ops dicts

ARITHMETIC_PREDICATES_GRAMMAR = """
?arithmetic_predicate: sum
  | arithmetic_predicate ">"  sum          -> gt
  | arithmetic_predicate ">=" sum          -> gte
  | arithmetic_predicate "<"  sum          -> lt
  | arithmetic_predicate "<=" sum          -> lte
  | arithmetic_predicate "==" sum          -> eq
  | arithmetic_predicate "!=" sum          -> neq
  | "(" arithmetic_predicate ")"
""" + ARITHMETIC_GRAMMAR

arithmetic_predicate_parser = lark.Lark(ARITHMETIC_PREDICATES_GRAMMAR, start="arithmetic_predicate")

arithmetic_predicate_ops = {
    **arithmetic_ops,
    "gt": lambda a, b: a > b,
    "gte": lambda a, b: a >= b,
    "lt": lambda a, b: a < b,
    "lte": lambda a, b: a <= b,
    "eq": lambda a, b: a == b,
    "neq": lambda a, b: a != b,
}

arithmetic_predicate_compile_ops = generate_compiler_ops(arithmetic_predicate_ops)

def compile_arithmetic_predicate(text: str):
    return compile((arithmetic_predicate_compile_ops, arithmetic_predicate_parser), text)


assert(compile_arithmetic_predicate("0 == 0")({}))
assert(compile_arithmetic_predicate("0 != -1")({}))
assert(compile_arithmetic_predicate("0 > -1")({}))
assert(compile_arithmetic_predicate("2 >= 2")({}))
assert(compile_arithmetic_predicate("-2 < 2")({}))
assert(compile_arithmetic_predicate("0 <= 0")({}))
test(arithmetic_predicate_ops, arithmetic_predicate_parser, "(a ** 2 ** 2 - 10) > b * (a ** (c / 2))", {'a': 100, 'b': 200, 'c': 3}, True)

#
# ====================================================================================================
# Arithmetic calculations and predicates and logic functions on environment with variable values.
# ====================================================================================================
#

ARITHMETIC_AND_LOGIC_PREDICATES_GRAMMAR = """
?disjunction: conjunction
  | disjunction "or" conjunction       -> or

?conjunction: negation
  | conjunction "and" negation         -> and

?negation: arithmetic_predicate
  | "not" negation                     -> not
  | "(" disjunction ")"
""" + ARITHMETIC_PREDICATES_GRAMMAR

arithmetic_and_logic_predicate_parser = lark.Lark(ARITHMETIC_AND_LOGIC_PREDICATES_GRAMMAR, start="disjunction")

arithmetic_and_logic_predicate_ops = {
    **arithmetic_predicate_ops,
    "or": lambda a, b: a or b,
    "and": lambda a, b: a and b,
    "not": lambda b: not b,
}

arithmetic_and_logic_predicate_compile_ops = generate_compiler_ops(arithmetic_and_logic_predicate_ops)

def compile_arithmetic_and_logic_predicate(text: str):
    return compile((arithmetic_and_logic_predicate_compile_ops, arithmetic_and_logic_predicate_parser), text)

test_arith_logic = lambda *args, **kvargs: test(arithmetic_and_logic_predicate_ops, arithmetic_and_logic_predicate_parser, *args, **kvargs)

test_arith_logic("a < b and (a == b or a * c >= b)", {'a': 100, 'b': 200, 'c': 3}, True)
test_arith_logic("a < b and a == b or a * c >= b", {'a': 100, 'b': 200, 'c': 3}, True)
test_arith_logic(
    "f * g + e > d and a < b and (a == b or a * c >= b)",
    {'a': 100, 'b': 200, 'c': 3, 'd': 9768, 'e': 2334, 'g': -1, 'f': -5.5},
    False
)


#
# ====================================================================================================
# Generate
# ====================================================================================================
#

def wrap(s):
    return "("+s+")"

def rand_join(j_arr, v_arr, count):
    v_arr = [wrap(x) for x in v_arr]
    v = [random.choice(v_arr) for i in range(count)]
    j = [random.choice(j_arr) for i in range(count-1)]
    x = [v[int(i/2)] if i%2==0 else j[int(i/2)] for i in range(count*2-1)]
    return ''.join(x)

def rand_join_pairs(j_arr, v_arr, count):
    v_arr = [wrap(x) for x in v_arr]
    return [random.choice(v_arr) + random.choice(j_arr) + random.choice(v_arr) for i in range(count)]

s2 = rand_join_pairs(["+", "-", "*", "/"], ["x", "y", "z", "1", "2", "3", "4"], 100)
s1 = rand_join_pairs(["==", ">", "<", ">=", "<=", "!="], s2, 100)
s = rand_join(["and", "or"], s1, 200)
e = {'x': 9875.7896, 'y': 876.976, 'z': -876.09}
test_arith_logic(s, e, True)

def rand_opt(s, prob=0.2):
    return s if random.random() < prob else ""

def rand_join_depth(j2_arr, j1_arr, v_arr, min_depth, max_depth, rand_depth=0.8):
    if min_depth == 0 and random.random() > rand_depth:
        max_depth = 0
    else:
        if min_depth > 0:
            min_depth -= 1
        max_depth -= 1

    v1 = random.choice(v_arr) if max_depth == 0 else rand_join_depth(j2_arr, j1_arr, v_arr, min_depth, max_depth, rand_depth)
    v2 = random.choice(v_arr) if max_depth == 0 else rand_join_depth(j2_arr, j1_arr, v_arr, min_depth, max_depth, rand_depth)
    return rand_opt(random.choice(j1_arr)) + v1 + random.choice(j2_arr) + rand_opt(random.choice(j1_arr)) + v2


s2 = [rand_join_depth(["+", "-", "*", "/"], ["", " -"], ["x", "y", "z", "1", "2", "3"], 3, 5, 0.9) for i in range(10)]
s1 = rand_join_pairs([" == ", " > ", " < ", " >= ", " <= ", " != "], s2, 10)
s = rand_join_depth(["\nor\n", "\nand\n"], ["", "not "], s1, 3, 5, 0.9)
test_arith_logic(s, e, False, verbose=False, debug=True)



#
# ====================================================================================================
# Pipe notation with functions
# ====================================================================================================
#

PIPES_AND_FUNCTIONS_GRAMMAR = """
?composition: function
  | function "|" composition

?function: CNAME
  | "(" composition ")"

%import common.CNAME

%import common.WS_INLINE
%import common.NEWLINE
%ignore WS_INLINE
%ignore NEWLINE
"""

pipes_and_functions_parser = lark.Lark(PIPES_AND_FUNCTIONS_GRAMMAR, start="composition")

def compose(g, f) -> Callable:
    return lambda x: f(g(x))

#TODO: Can I use functors for compilation?
pipes_and_functions_ops = {
    "composition": compose,
    "add_1": lambda x: x + 1,
    "mul_2": lambda x: x * 2,
    "neg": lambda x: -x,
}

pipes_and_functions_compile_ops = generate_compiler_ops(pipes_and_functions_ops)

def compile_pipes_and_functions(text: str):
    return compile((pipes_and_functions_compile_ops, pipes_and_functions_parser), text)

f = compile_pipes_and_functions("|\n".join(["(add_1 | mul_2 | neg)"]*200))
#print(f(1))

def test_pipes_and_functions(text, env, result):
    test(pipes_and_functions_ops, pipes_and_functions_parser, text, env, result)


test_pipes_and_functions("|".join(["(add_1 | mul_2 | neg)"]*200), 1, 2678230073764983792569936820568604337537004989637988058835626)

#TODO: Implement functions definition like (_ + 3) and other functors



"""
=====================================================================================================
Query

    Query vs. Equation?
    Query is functional processing pipe starting on current object.
    Equation is named formula that contains arithmetic operations, resource values on current object or global root.

Pipe notation

    List of functions separated with vertical bar "|".
    Each function receive single argument or list and return single object, value or list.
    To apply single-argument function to list - explicitly use "map".
    Argument of first function is single current object.
    Result of previous function pass to next one.
    Output of last function is result of the query.

Parentheses

    Functions linked with pipe represent one function.
    So just surround them with parentheses - it became single function that can be used with map or recursive.

Path selector

    Path selector cat takes objects or values.

    _ - current object
    / - root object
    .parent, ../ - parent object
    .objects, .[] - child objects
    .source.<res_name>, .src.<res_name> - source of <res_name> for this object
    .users.<res_name> - users of <res_name> of this object
    .resources.<res_name>, .res.<res_name> - value of total of <res_name>
    .used.<res_name> - value of used of <res_name>
    .free.<res_name> - value of free of <res_name>

Map functor

    If function return list of objects to apply next function to every object - use map:
    Example - get cpu from every child object: .[] | map .res.cpu

Join function

    If mapped function return list for every object - then you got list of lists into output.
    Join converts it into simple flat list.
    It does nothing if not required.
    Example - get cpu users of from every child object: .[] | map .users.cpu | join
    TODO: consider apply join by default.

Predicate

    Function that returns bool.

    Can use logic operations on top of boolean functions.

Arithmetic function from values on single object

    Can use fileds of input object or input value.
    Input value marked with underscore: "_".
    Example: _ + 10

Filter functor

    Applies to list of objects and throw out objects that does not match predicate function.

Functions on lists:
    count
    sum
    min
    max

Recursive search

    Path selector returns one object or list of objects or value or list of values.
    If it is required to got through depth of links - use recursive search.
    It recursively applies provided function to it's output while output is not empty.
    And the whole function returns all objects that match predicate from every level.
    Recursive functor takes two arguments:
    1-st is required - function that will be applied recursively
    2-nd is optional - filter predicate

=====================================================================================================
""" 

#TODO: Do not undestand how to use jq or jinja2 or any other embeddable lang here for queries
# So first implement simple primitive hand-made one and then find a way to use others.


class Value:
    """
        Consider equation V = n*(x - y)/(z + w) and constraint V >= 10.
        If V will be calculated into numerical value and then constraint checked,
        then we get no information about what free variable values we should increase or decrease
        to finally match the constraint.

        Then one way (that I see) is to link result value with all it's sources with labeled linkes.
        Labels are proportionality direction: direct or inverse.
        Also can be added labels like proportionality rank: linear, polynomial, exponential.
        Using this links (I hope) solver will be able to infer what free variable should be increased or decreased.
        And in this application all modifications of free variables, like add one more hdd disk,
        will have cost in terms of optimization target value, like financial cost.
        So solver (again, I hope) will be able to select modification that makes maximum(impact/cost). 

    """
    def __init__(self):
        pass


def compile_query(q: str):
    pass





"""
=====================================================================================================
Object type (prototype, description, ...)
=====================================================================================================
"""

class ObjectType:
    def __init__(self, name: str, categories: List[List[str]], requires: List, provides: List, properties: Dict):

        # Unique name for object type
        self.name = name
        
        # List of categories
        # Predicates can be calculated with categories as args
        self.categories = categories
        
        # List of requirements
        # Each requirement contains:
        #   resource name - string, key of dict
        #   query - returns objects to select resource source from
        #   value of required resource - simple integer
        #
        # For every requirements scheduler 
        self.requires = {}
        
        # 
        self.provides = {}

        # property is named query which cached value goes to resources
        # while it is resource it should have unit, but units come from queried values
        self.properties = {}



"""
=====================================================================================================
Global Properties
=====================================================================================================
"""

global_properties = {
    # (name, predicate) : query
}


def add_property_if_applicable(obj_type: ObjectType, name: str, predicate: str, query: str):
    if name in obj_type.properties or name in obj_type.provides:
        raise f'ERROR: add_property_if_applicable({{.name={obj_type.name}}}, {name}, ...): resource "{name}" is already defined in property or provides'
    p = compile_cat_predicate(predicate)
    cats = parse_categories(obj_type.categories)
    if p(cats):
        obj_type.properties[name] = query


def preprocess_object_types(type_list: List[ObjectType]) -> List[ObjectType]:
    """
        Consider initial ObjectType as immutable and generate usable ObjectType with properties added, categories parsed and queries compiled
    """
    return []





"""
=====================================================================================================
Object (with uuid)
=====================================================================================================
"""

class Object:
    def __init__(self, type: ObjectType):
        self.uuid = uuid.uuid4()

        # description from it was created
        self.type = type

        # Initial values of reqources calculated from provides and properties, by resource name.
        # If property duplicates resource name provided by provides - it is error.
        self.resources = {}

        # Used amount of resources, by resource name
        self.used_resources = {}

        # uuid of parent object where this object is in objects list
        self.parent: Object = None

        # owning list of child objects
        self.objects: List[Object] = []

        # objects where this object uses resources by resource name, uplinks
        self.source: Dict[str, Object] = {} 

        # objects that use this object by resource that is consumed
        self.users: Dict[str, List[Object]] = {}


objects_by_uuid : Dict[uuid.UUID, Object] = {}






"""
=====================================================================================================
Variables

    Global value that can vary during optimization process.



Equations




Constraints



=====================================================================================================
"""





"""
=====================================================================================================
Requirements
=====================================================================================================
"""

