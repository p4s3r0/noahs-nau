from z3 import Int, Solver, Or, sat, Distinct


stats = {
        "cat" : {
            "eating": "carnivores",
            "property": None,
            "weight": 1 
        },
        "elephant": {
            "eating": "herbivores",
            "property": None,
            "weight": 3 
        },
        "sparrow": {
            "eating": "herbivore",
            "property": None,
            "weight": 1
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

