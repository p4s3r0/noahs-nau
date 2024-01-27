# Noé's Nau

## Input Format

Comments are marked with a `#` infront of the line and empty lines are ignored. Special setion markers are marked with a `!` followed by the specifier (`nau_size`, `animals` and `supplies`)

### Nau Size

The Nau size is determined by the parameter following `! nau_size`. The parameter has to be an integer which is dividible by `6`, since the Nau needs to be symmetric (dividible by 2) and each compartment has storage for 3 animals (dividible by 3). 

Example Nau size config

```text
# Possible sizes are 6, 12, 18, ...
! nau_size 6
```

### Animals

To determine the animals we need to place onto the nau, we need to specify the animal declaration block by placing `! animals` at the very top of the animals declarations. For each animal, we need a single line with exactly two parameters. The unique name `<NAME>` of the animal and the according species `<SPECIES>`. The available species are the follows:

```python
"Cat"     : { "eating": CARNIVORE, "weight": 1 },
"Sparrow" : { "eating": HERBIVORE, "weight": 1 },
"Fox"     : { "eating": OMNIVORE , "weight": 1 },
"Lion"    : { "eating": CARNIVORE, "weight": 2 },
"Horse"   : { "eating": HERBIVORE, "weight": 2 },
"Elephant": { "eating": HERBIVORE, "weight": 3 },
"Dodo"    : { "eating": OMNIVORE , "weight": 1, "property": SHY  },
"Turtle"  : { "eating": OMNIVORE , "weight": 2, "property": SLOW },
```

Example animals declaration block:

```text
! animals
Minky Cat
Benjamin Elephant
Timy Dodo
```

### Supplies

Supplies are a special type of carriage. We define the supplies by opening a `! supplies` block and defining each supply with an unique name. The weight of each supply is always 2. 

Example supplies declaration block:

```text
! supplies
Meat
Seeds
Water
SupplyName1
```



## Implementation

### 1. General restrictions

The Nau has `<NAU_SIZE>` positions and each position can only be taken by exactly one animal.

```python
# positions of animals have to be on the arch | 4 -> Since two left and two right
for animal in animals:
    s.add(animals[animal].position > 0, animals[animal].position <= NAU_SIZE)

# one position cannot be taken by different animals
s.add(z3.Distinct([animals[animal].position for animal in animals]))
```




Each position belongs to a specific compartment. Positions 1,2,3 map to compartment 1 and 4,5,6 to compartment 2 and so on. This was specified with the following lines of code

```python
for animal in animals:
    for pos in range(1, NAU_SIZE+1, 1):
        if pos % 3 == 0:
            s.add(z3.Implies(animals[animal].position == pos, animals[animal].compartment == pos // 3))
        else:
            s.add(z3.Implies(animals[animal].position == pos, animals[animal].compartment == pos // 3 + 1))
```

### 2. Nau Tilt

The Nau can tilt to left or right, 2 steps each. If we place an animal on the right side, the nau tilts to the right by the animals weight steps. This was implemented with the following lines:


```python
# if animal on the left side -> tilt boat to left (subtract weight of total weight)
# if animal on the right side -> tilt boat to right (add weight to total weight)
for animal in animals:
    s.add(z3.If(animals[animal].position <= NAU_SIZE/2, animals[animal].tilt == -animals[animal].weight, animals[animal].tilt == animals[animal].weight))

# calculate tilt of boat (to right or left)
nau_tilt = sum([animals[animal].tilt for animal in animals])
s.add(nau_tilt < 3, nau_tilt > -3)
```

### 3. Small Herbivores

Carnivores or omnivores can only be with other herbivores if the herbivore is larger (has more weight) than the carnivore. This was realized by the following lines of code.


```python
for carnivor_or_omnivore in animals:
    if animals[carnivor_or_omnivore].eating != Const.CARNIVORES and animals[carnivor_or_omnivore].eating != Const.OMNIVORES: continue
    for herbivore in animals:
        if animals[herbivore].eating != Const.HERBIVORES: continue
        if animals[herbivore].weight <= animals[carnivor_or_omnivore].weight:
            s.add(z3.Distinct(animals[carnivor_or_omnivore].compartment, animals[herbivore].compartment))
```



### 4. Supplies

Supplies cannot be together with herbivores or omnivores.

```python
for supply in animals:
    if animals[supply].family != "Supply": continue
    for animal in animals:
        if animals[supply].name == animals[animal].name: continue
        if animals[animal].eating == Const.HERBIVORES or animals[animal].eating == Const.OMNIVORES:
            s.add(z3.Distinct(animals[supply].compartment, animals[animal].compartment))
```

### 5. Shy Animals
Shy animals cannot be in compartments with omnivores or carnivores, nor can they be in a neighbouring compartment with omnivores or carnivores. I defined neighbouring as two compartments on the same side of the nau (left or right) which are next to each other (compartment 2 is neighbouring with 1 and 3 if the nau has 6 compartments).


```python
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
```

### 6. Score

The score is computed by the following rules:

- Each animal gives on point.
- Two of a kind receives five points.
- Having at least one of each family awards five points.
- Having at least one slow animal gives three points.
- Having at least one shy animal gives five points.

Since `z3` does not have a "optimize this variable" method, I had to implement it myself. I produce every possible animals combination, compute the score and check if it is satisfiable. For each combination I check, if the score is better than the previous best one and if it is satisfiable, if yes, i replace the previous "best" model with new current one. 


## Test Instances

|File|Task|Result|
|-|-|-|
|`tests/submission/1_three_animals`      |Animals: 3, Nau Size: 6 |All Fit|
|`tests/submission/2_five_animals`       |Animals: 5, Nau Size: 6 |All Fit|
|`tests/submission/3_seven_animals`      |Animals: 7, Nau Size: 12|All Fit|
|`tests/submission/4_eight_animals`      |Animals: 8, Nau Size: 12|All Fit|
|`tests/submission/5_not_all_animals`    |Animals: 7, Nau Size: 6 |Only 6 Fit, Nau Size too big|
|`tests/submission/6_not_all_carni_herbi`|Animals: 6, Nau Size: 6 |Only 5 Fit, Carnivores not with Herbivores|
|`tests/submission/7_dodos_all_animals`  |Animals: 7, Nau Size: 12|One Dodo does not Fit, one animal for each species|
|`tests/submission/8_best_not_all`  |Animals: 5, Nau Size: 12|Best solution is without one cat, since exactly 2 cats =+5 points|



