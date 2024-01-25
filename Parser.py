import Animal

def parseFile(file):

    animals = dict()
    nau_size = -1
    parsing_animals = False
    parsing_supplies = False
    
    with open(file, 'r') as f:
        for line in f:
            line = line.replace('\n', '').split()
            if len(line) == 0: continue
            if line[0] == '#': continue
            if line[0] == '!' and line[1] == "animals":
                parsing_animals = True
                parsing_supplies = False
                continue

            if line[0] == '!' and line[1] == "supplies":
                parsing_animals = False
                parsing_supplies = True
                continue

            if line[0] == '!' and line[1] == "nau_size":
                nau_size = int(line[2])


            if parsing_animals:
                animals[line[0]] = Animal.Animal(name=line[0], family=line[1])

            if parsing_supplies:
                animals[line[0]] = Animal.Animal(name=line[0], family="Supply")

            

    if nau_size == -1:
        print("nau size was not defined")
        exit()

    return animals, nau_size


