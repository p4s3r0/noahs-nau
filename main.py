import sys

import Animal as Animal
import Parser
import Const
import Solver
import itertools

def print_model(m, curr_animals):
    for animal in curr_animals:
        print(f"[{str(m[curr_animals[animal].compartment]):<2}|{str(m[curr_animals[animal].position]):<2}] {curr_animals[animal].name:<10} | weight: {curr_animals[animal].weight}")
    print(f"nau tilt: {sum(int(str(m[curr_animals[animal].tilt])) for animal in curr_animals)}")



def calcScore(combination, init_animals):
    # each animal gives 1 point
    score = len(combination)

    # two of a kind receives five points,
    species = {
        "Cat": 0,
        "Elephant": 0,
        "Sparrow": 0,
        "Fox": 0,
        "Dodo": 0,
        "Horse": 0,
        "Turtle": 0,
        "Lion": 0,
    }
    for animal in combination:
        species[combination[animal].family] = species[combination[animal].family] + 1
    for spec in species:
        if species[spec] >= 2: 
            score += 5

    # one of each species
    one_of_each_species = True
    species_init = {
        "Cat": 0,
        "Elephant": 0,
        "Sparrow": 0,
        "Fox": 0,
        "Dodo": 0,
        "Horse": 0,
        "Turtle": 0,
        "Lion": 0,
    }
    for animal in init_animals:
        species_init[init_animals[animal].family] = species_init[init_animals[animal].family] + 1

    for spec in species:
        if species_init[spec] >= 1 and species[spec] == 0:
            one_of_each_species = False
    
    if one_of_each_species:
        score += 5

    
    
    # having at least one slow animal gives three points
    slow_animal = False
    for animal in combination:
        if combination[animal].property == Const.SLOW:
            slow_animal = True
    if slow_animal:
        score += 3

    # having at least one shy animal gives five points.
    shy_animal = False
    for animal in combination:
        if combination[animal].property == Const.SHY:
            shy_animal = True
    if shy_animal:
        score += 5

    return score



def main():
    if len(sys.argv) != 2:
        print(f"Usage: python3 main.py <INPUT_FILE>")
        exit()


    # get input file config
    init_animals, NAU_SIZE = Parser.parseFile(sys.argv[1])

    # get combinations of input file
    listed_animals = [init_animals[animal].name for animal in init_animals]
    animals_combinations = list()
    for i in range(1, len(listed_animals)+1):
        animals_combinations.append(list(itertools.combinations(listed_animals, i)))

    # iterate over combinations
    best_score = 0
    best_model = None
    comb_i = 0
    for curr_comb_length in animals_combinations:
        for curr_comb in curr_comb_length:
            comb_i += 1
            # create animals struct
            curr_animals = dict()
            for animal_name in curr_comb:
                curr_animals[animal_name] = init_animals[animal_name]
            # calculate score
            score = calcScore(combination=curr_animals, init_animals=init_animals)
            # check if current comb is satisfiable
            m = Solver.solve(animals=curr_animals, NAU_SIZE=NAU_SIZE)

            print(f"[{comb_i:>3}] Score: {score:>2}  |  {'UNSAT' if m == 'UNSAT' else 'SAT':^6}  |  Combination: {curr_comb}")

            if m == "UNSAT": 
                continue

            if score > best_score:
                best_score = score
                best_model = m
                best_animals = curr_animals
        
    print("best score:", best_score)
    print_model(m=best_model, curr_animals=best_animals)
            
            
    

if __name__ == "__main__":
    main()
