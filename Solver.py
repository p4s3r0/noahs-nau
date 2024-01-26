import z3
import Const
    
def solve(animals, NAU_SIZE):
    s = z3.Solver()

    # positions of animals have to be on the arch | 4 -> Since two left and two right
    for animal in animals:
        s.add(animals[animal].position > 0, animals[animal].position <= NAU_SIZE)

    # compartments are defined through to the position. position 1,2,3 are compartment 1. 
    # position 4,5,6 are compartment 2....
    for animal in animals:
        for pos in range(1, NAU_SIZE+1, 1):
            # weird mapping
            if pos % 3 == 0:
                s.add(z3.Implies(animals[animal].position == pos, animals[animal].compartment == pos // 3))
            else:
                s.add(z3.Implies(animals[animal].position == pos, animals[animal].compartment == pos // 3 + 1))

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
    for carnivor_or_omnivore in animals:
        if animals[carnivor_or_omnivore].eating != Const.CARNIVORES and animals[carnivor_or_omnivore].eating != Const.OMNIVORES: continue
        for herbivore in animals:
            if animals[herbivore].eating != Const.HERBIVORES: continue
            if animals[herbivore].weight <= animals[carnivor_or_omnivore].weight:
                s.add(z3.Distinct(animals[carnivor_or_omnivore].compartment, animals[herbivore].compartment))



    # 3. Supplies cannot be together with herbivores or omnivores.
    for supply in animals:
        if animals[supply].family != "Supply": continue
        for animal in animals:
            if animals[supply].name == animals[animal].name: continue
            if animals[animal].eating == Const.HERBIVORES or animals[animal].eating == Const.OMNIVORES:
                s.add(z3.Distinct(animals[supply].compartment, animals[animal].compartment))



    # 4. Shy animals cannot be in compartments with omnivores or carnivores, nor can they be in a 
    # neighbouring compartment with omnivores or carnivores.
    #TODO: neighbouring
    for shy_animal in animals:
        if animals[shy_animal].property != Const.SHY: continue
        for carnivor_or_omnivore in animals:
            if animals[carnivor_or_omnivore].eating != Const.CARNIVORES and animals[carnivor_or_omnivore].eating != Const.OMNIVORES: continue
            if animals[shy_animal].name == animals[carnivor_or_omnivore].name: continue
            s.add(z3.Distinct(animals[shy_animal].compartment, animals[carnivor_or_omnivore].compartment))
    
    # if compartments do not have neighbours, skip
    if NAU_SIZE > 6:
        # top neighbour check
        for c in range(1, NAU_SIZE // 3 + 1, NAU_SIZE // 6):
            for animal in animals:
                for carnivor_or_omnivore in animals:
                    if animals[carnivor_or_omnivore].eating != Const.CARNIVORES and animals[carnivor_or_omnivore].eating != Const.OMNIVORES: continue
                    s.add(z3.If(animals[animal].compartment == c, 
                                z3.If(animals[animal].property == Const.SHY, 
                                    animals[carnivor_or_omnivore].compartment != c+1, True), True))     

        # bottom neighbour check
        for c in range(2, NAU_SIZE // 3 + 1, NAU_SIZE // 6):
            for animal in animals:
                for carnivor_or_omnivore in animals:
                    if animals[carnivor_or_omnivore].eating != Const.CARNIVORES and animals[carnivor_or_omnivore].eating != Const.OMNIVORES: continue
                    s.add(z3.If(animals[animal].compartment == c, 
                                z3.If(animals[animal].property == Const.SHY, 
                                    animals[carnivor_or_omnivore].compartment != c-1, True), True))     



    if s.check() == z3.sat:
        return s.model()
    else:
        return "UNSAT"
