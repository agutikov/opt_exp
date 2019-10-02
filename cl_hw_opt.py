#!/usr/bin/env python3

import uuid
from typing import List, Dict, Tuple, Callable, Any
import lark
from pprint import pprint

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

def gen_cat_predicate_eval_single(cat: List[str]) -> Callable[[List[List[str]]], bool]:
    return (lambda cap_cat: lambda x: cat_contains_subcat_from_list(cap_cat, x))(cat)

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

?item: NAME            -> call
  | "(" dis ")"

NAME: /{}/

%import common.WS
%ignore WS
""".strip()

def get_logic_grammar_parser(call_regex):
   return lark.Lark(LOGIC_GRAMMAR.format(call_regex))

#TODO: optimize for fast eval of logical ops for multiple args, like "a or b or c or d"

def compile_predicate(tree, ops) -> Callable[[Any], bool]:
    return ops[tree.data](tree, ops)

def compile_1_arg_func(func, tree, ops) -> Callable[[Any], bool]:
    p = compile_predicate(tree.children[0], ops)
    return (lambda a, f: lambda x: f(a(x)))(p, func)

def compile_2_arg_func(func, tree, ops) -> Callable[[Any], bool]:
    lhs = compile_predicate(tree.children[0], ops)
    rhs = compile_predicate(tree.children[1], ops)
    return (lambda lhs, rhs, f: lambda x: f(lhs(x), rhs(x)))(lhs, rhs, func)

default_logic_predicate_ops = {
    "or": lambda tree, ops: compile_2_arg_func(lambda a, b: a or b, tree, ops),
    "and": lambda tree, ops: compile_2_arg_func(lambda a, b: a and b, tree, ops),
    "not": lambda tree, ops: compile_1_arg_func(lambda b: not b, tree, ops),
}

#
# ====================================================================================================
# Combine category-subcategory matching and logic operations
# ====================================================================================================
#

cat_logic_grammar_parser = get_logic_grammar_parser(r"([a-zA-Z0-9_]+\.)*[a-zA-Z0-9_]+")

def compile_cat_predicate(p: str) -> Callable[[List[List[str]]], bool]:
    tree = cat_logic_grammar_parser.parse(p)
    ops = {
        **default_logic_predicate_ops,
        "call": lambda tree, ops: gen_cat_predicate_eval_single(parse_cat(tree.children[0]))
    }
    return compile_predicate(tree, ops)


assert(compile_cat_predicate("a.b")(parse_categories("a.b.c, x.y.z")))

c = parse_categories("hw.disk.type.ssd, hw.vendor.intel, hw.disk.func.discard")
p = compile_cat_predicate("hw.disk and not hw.disk.type.nvme or not hw.disk.func.discard and hw.vendor.intel")
assert(p(c))

c = parse_categories("hw.disk.type.nvme, hw.vendor.intel, hw.disk.func.discard")
p = compile_cat_predicate("hw.disk and not (hw.disk.type.nvme or not hw.disk.func.discard) and hw.vendor.intel")
assert(not p(c))

assert(compile_cat_predicate("a.b and not (x.y.f or a.b.z) and not x.y.t")(parse_categories("a.b.c, x.y.z")))
assert(not compile_cat_predicate("a.b.c.d or x.y.z.r or not x.y.z")(parse_categories("a.b.c, x.y.z")))


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
        #   query:
        #     selector of single object
        #     resource name
        #   value
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

#TODO: Consider initial ObjectType as immutable and generate usable OpbjectType with properties added, categories parsed and queries compiled

def add_property_if_applicable(obj_type: ObjectType, name: str, predicate: str, query: str):
    if name in obj_type.properties or name in obj_type.provides:
        raise f'ERROR: add_property_if_applicable({{.name={obj_type.name}}}, {name}, ...): resource "{name}" is already defined in property or provides'
    p = compile_cat_predicate(predicate)
    cats = parse_categories(obj_type.categories)
    if p(cats):
        obj_type.properties[name] = query






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
        self.parent = None

        # owning list of child objects
        self.objects = []

        # objects where this object uses resources by resource name, uplinks
        self.uses = {} 

        # objects that use this object by resource that is consumed
        self.users = {}





#TODO: Do not undestand how to use jq or jinja2 or any other embeddable lang here for queries
# So first implement simple primitive hand-made one and then find a way to use others.

"""
=====================================================================================================
Tree Element Selector (object selector)

    Selector: path specifyer + type predicate + traverse mode + select mode, |-separated, repeatable

    Selector always starts on it's own context:
    if it is in property of object - then starts from this object

    Type predicates are already implemented
    Format: filter <predicate>

    Path: starts with dot and then one of [parent, objects, uses[<res_name>], users[<res_name>]]
    Examples: .parent, .objects, .uses[ram], .users[ram]

    Traverse mode: default or deapth-search


    Select mode: Single element (any of them) or all elements.
    Any element - for requirements.
    All elements - for summarization on resources.
    Default is all elements.
    For any element - use word any. 

Query language

    Query: object selector + (optional) resource name + function, |-separated

    Resource getter format: get <res_name>

    Functions:
        count
        sum
    

    query for resources - in properties
    query for object - in requirement

=====================================================================================================
""" 






"""
=====================================================================================================
Constraints
=====================================================================================================
"""




"""
=====================================================================================================
Requirements
=====================================================================================================
"""

