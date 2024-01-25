import Animal as Animal
import z3
import Parser

NAU_SIZE = 12
def main():
    #TODO: Input file as command line argument
    animals = Parser.parseFile("inp.txt")

    s = z3.Solver()

    # positions of animals have to be on the arch | 4 -> Since two left and two right
    for animal in animals:
        s.add(animals[animal].position > 0, animals[animal].position <= NAU_SIZE)

    # compartments are defined through to the position. position 1,2,3 are compartment 1. 
    # position 4,5,6 are compartment 2....
    for animal in animals:
        s.add(animals[animal].compartment == animals[animal].position / 3 + 1)

    # if animal on the left side -> tilt boat to left (subtract weight of total weight)
    # if animal on the right side -> tilt boat to right (add weight to total weight)
    for animal in animals:
        s.add(z3.If(animals[animal].position <= NAU_SIZE/2, animals[animal].tilt == -animals[animal].weight, animals[animal].tilt == animals[animal].weight))
    
    # calculate tilt of boat (to right or left)
    nau_tilt = sum([animals[animal].tilt for animal in animals])
    s.add(nau_tilt < 3, nau_tilt > -3)

    # one position cannot be taken by different animals
    s.add(z3.Distinct([animals[animal].position for animal in animals]))


    # 2. Carnivores or omnivores can only be with other herbivores if the herbivore is larger (has more weight) than the 
    # carnivore (e.g., a cat can be together with horses, but not sparrows, and lions can be together with other lions and elephants).
    #TODO

    # 3. Supplies cannot be together with herbivores or omnivores.
    for supply in animals:
        if animals[supply].family != "Supply": continue
        for animal in animals:
            if animals[supply].name == animals[animal].name: continue
            if animals[animal].eating == "herbivores" or animals[animal].eating == "omnivores":
                s.add(z3.Distinct(animals[supply].compartment, animals[animal].compartment))



    if s.check() == z3.sat:
        m = s.model()
        for animal in animals:
            print(f"[{str(m[animals[animal].compartment]):<2}|{str(m[animals[animal].position]):<2}] {animals[animal].name:<10} | weight: {animals[animal].weight}")
        print(f"nau tilt: {sum(int(str(m[animals[animal].tilt])) for animal in animals)}")
    else:
        print("unsat")

if __name__ == "__main__":
    main()
