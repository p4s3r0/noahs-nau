from z3 import Int


stats = {
        "Cat" : {
            "eating": "carnivores",
            "property": None,
            "weight": 1 
        },
        "Elephant": {
            "eating": "herbivores",
            "property": None,
            "weight": 3 
        },
        "Sparrow": {
            "eating": "herbivore",
            "property": None,
            "weight": 1
        },
        "Foxes": {
            "eating": "omnivores",
            "property": None,
            "weight": 1
        },
        "Dodos": {
            "eating": "omnivores",
            "property": "shy",
            "weight": 1
        },
        "Horses": {
            "eating": "herbivores",
            "property": None,
            "weight": 2
        },
        "Turtles": {
            "eating": "omnivores",
            "property": "slow",
            "weight": 2
        },
        "Lions": {
            "eating": "carnivores",
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

