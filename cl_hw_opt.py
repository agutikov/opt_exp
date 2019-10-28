#!/usr/bin/env python3

import uuid
from typing import List, Dict, Tuple, Callable, Any
import lark
from pprint import pprint
from inspect import signature, Parameter
import time
import random
import functools


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
        raise Exception(f'ERROR: add_property_if_applicable({{.name={obj_type.name}}}, {name}, ...): resource "{name}" is already defined in property or provides')
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

