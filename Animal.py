from z3 import Int
import Const

stats = {
        "Cat" : {
            "eating": Const.CARNIVORES,
            "property": None,
            "weight": 1 
        },
        "Elephant": {
            "eating": Const.HERBIVORES,
            "property": None,
            "weight": 3 
        },
        "Sparrow": {
            "eating": Const.HERBIVORES,
            "property": None,
            "weight": 1
        },
        "Fox": {
            "eating": Const.OMNIVORES,
            "property": None,
            "weight": 1
        },
        "Dodo": {
            "eating": Const.OMNIVORES,
            "property": Const.SHY,
            "weight": 1
        },
        "Horse": {
            "eating": Const.HERBIVORES,
            "property": None,
            "weight": 2
        },
        "Turtle": {
            "eating": Const.OMNIVORES,
            "property": Const.SLOW,
            "weight": 2
        },
        "Lion": {
            "eating": Const.CARNIVORES,
            "property": None,
            "weight": 2
        },
        "Supply": {
            "eating": "",
            "property": None,
            "weight": 2
        }
    }



class Animal:
    def __init__(self, name, family) -> None:
        self.name = name
        self.family = family
        self.eating = stats[family]["eating"]
        self.property = stats[family]["property"]
        self.weight = stats[family]["weight"]

        self.position = Int(f"{name}_position")
        self.tilt = Int(f"{name}_tilt")
        self.compartment = Int(f"{name}_compartment")

