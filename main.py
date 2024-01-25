import Animal as Animal
import z3

NAU_SIZE = 4
def main():
    # TODO: read in file
    animals = {
        "cat": Animal.Animal(name="Minky", family="cat"),
        "elephant": Animal.Animal(name="Ludwig", family="elephant"),
        "sparrow": Animal.Animal(name="Karl", family="sparrow"),
        "sparrow2": Animal.Animal(name="Karl2", family="sparrow")
    }

    s = z3.Solver()

    # positions of animals have to be on the arch | 4 -> Since two left and two right
    for animal in animals:
        s.add(animals[animal].position > 0, animals[animal].position <= NAU_SIZE)

    # if animal on the left side -> tilt boat to left (subtract weight of total weight)
    # if animal on the right side -> tilt boat to right (add weight to total weight)
    for animal in animals:
        s.add(z3.If(animals[animal].position % 2 == 0, animals[animal].tilt == -animals[animal].weight, animals[animal].tilt == animals[animal].weight))
    
    # calculate tilt of boat (to right or left)
    nau_tilt = sum([animals[animal].tilt for animal in animals])
    s.add(nau_tilt < 3, nau_tilt > -3)

    # one position cannot be taken by different animals
    s.add(z3.Distinct([animals[animal].position for animal in animals]))

    if s.check() == z3.sat:
        m = s.model()
        for animal in animals:
            print(f"[{m[animals[animal].position]}] {animals[animal].name:<10} , weight: {animals[animal].weight}")
        print(f"nau tilt: {sum(int(str(m[animals[animal].tilt])) for animal in animals)}")
    else:
        print("unsat")

if __name__ == "__main__":
    main()
