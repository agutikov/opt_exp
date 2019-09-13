#!/usr/bin/env python3


# all possible resources
resources_types = {
    "power": {"unit": "W"},

    "cpu_cores": {"unit": ""},
    "cpu_threads": {"unit": ""},
    "cpu_mhz": {"unit": ""},

    "ram": {"unit": "B"},

    "volume": {"unit": "B"},
    "bps": {"unit": "B/s"},
    "iops": {"unit": "s-1"},
}


# integer
# float
# bool
# enum
variables = {

}

#TODO: JSON schema :)))))))))))

object_template = {
    "categories": [],
    "name": "",
    
    "requires": {
        "objects": [
            {
                "name": "",
                "value": 0
            }
        ],
        "resources": [
            {
                "topology_context": "",
                "resource_id": {
                    "name": "",
                    "labels": [],
                },
                "value": 0.0
            }
        ]
    },

    "provides": {
        "topology_object": None,

        "objects": [
            {
                "name": "",
                "value": 0
            }
        ],
        "resources": [
            {
                "resource_id": {
                    "name": "",
                    "labels": [],
                },
                "value": 0.0
            }
        ]
    },

}


objects = [

]

#
# HW topology is to be produced during cluster construction
# collecting topology_objects of connected objects in hyerarchy
#


equation_relations = {
    # first operand == second operand 
    "==": {},

    # first operand < second operand 
    "<": {},

    # first operand > second operand 
    ">": {},

    # first operand <= second operand 
    "<=": {},

    # first operand >= second operand 
    ">=": {},

    # first operand contains second operand
    "in": {}
}

equation_functions = {
    "+": {},
    "-": {},
    "*": {},
    "/": {},
    "**": {},
}


constraints = [
    {
        "topology_context": "",
        "policy": "required",

        # predicate is tree with eq_relation in root and functions, variables and resources names in other nodes
        # example: ("<=", ("*", "bps", "iops"), ("*", "cpu_threads", "cpu_mhz"))
        "predicate": ("==", None, None)
    }
]


# 1 - select hw objects from objects and construct something
# 2 - verify constraints






# Optimization requirements




