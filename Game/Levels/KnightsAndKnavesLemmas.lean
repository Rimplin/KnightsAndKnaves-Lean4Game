import Game.Metadata
import Game.Levels.KnightsAndKnavesLemmas.L01_whydisjoint

import Game.Levels.KnightsAndKnavesLemmas.L02_inleft
import Game.Levels.KnightsAndKnavesLemmas.L02_Knight_NotKnave
import Game.Levels.KnightsAndKnavesLemmas.L03_inright
import Game.Levels.KnightsAndKnavesLemmas.L03_Knave_NotKnight
import Game.Levels.KnightsAndKnavesLemmas.L04_notinright
import Game.Levels.KnightsAndKnavesLemmas.L04_NotKnave_Knight
import Game.Levels.KnightsAndKnavesLemmas.notinleft
import Game.Levels.KnightsAndKnavesLemmas.L05_NotKnight_Knave

World "KnightsAndKnavesLemmas"
Title "Knights and Knaves, lemmas"
#check Set.mem_def
#check Set.instMembershipSet
Introduction 
"
-- maybe indicate stuff with headings, seems to get into it too quickly
We will introduce the knights and knaves puzzle here, and you will have to prove basic but important lemmas in the upcoming levels that will be used to solve the actual puzzles in the next world.

The setting is an island  in which certain inhabitants called 'knights' always tell the truth, and others called 'knaves' always lie.
Every inhabitant is either a knight or a knave, there is no third option.

/-
We can think of the set of knights and the set of knaves, denoted `Knights`, `Knaves` respectively. A set is a collection of 'entities' with a specified property. The set `Knight` would be the set of inhabitants of the island that are knights i.e satisfying the property of always telling the truth, the set `Knave` being the set of inhabitatns of the island that are knives i.e the ones that always lie. 

Note that in Lean, `Set K` means the set of objects of type `K`( this can be changed to something clearer?? think of clarity benefits of a change). Note that in each level, we will be considering two or three inhabitants of the island and will not be reasoning about the sets themselves but about these fixed inhabitants named `A`, `B`, `C`.
-/
Let `Knight` be the set of inhabitants that are knights, i.e always tell the truth.
Let `Knave` be the set of inhabitants that are knaves, i.e always lies.
In a proof state, this would look like:
```
Knight : Finset Inhabitant
Knave : Finset Inhabitant
```
`Knight` is a finite set where its elements are of type `Inhabitant` and they satisfy the propery of always telling the truth.
`Knave` is a fininte set there its elements are of type `Inhabitant` and they satisfy the property of always lying.

The statement `A ∈ Knight` is read as: `A` belongs to the finite set `Knight`(`A in Knight`), and it should be understood as 'A IS Knight' i.e 'A' always tells the truth. Then `A` is not a knave, i.e `A ∉ Knave`.
Similarly, the statement `A ∉ Knight` is read as: `A` doesn't belong to the finite set `Knight`(`A not in Knight`), and it should be understood as 'A ISNOT Knight'. What is `A` then? `A` has to be a knave, i.e `A ∈ Knave`.
The same reasoning applies to `x ∈ Knave`, `x ∉ Knave`.

Representing this more formally:
- Every inhabitant of the island is either a knight or a knave which is expressed as : A ∈ Knight ∨ A ∈ Knave.
- 'Knights' always tell the truth and 'Knaves' always lie. Clearly, no inhabitant can be both a knight and a knave. So the intersection of bothe sets is empty. Knight ∩ Knave = ∅. The two sets Knight Knave are disjoint.

The objective is to conclude who is a knight and who is a knave, based on the statements of several inhabitants. This will be done using logical reasoning. Every inhabitant will make at most one statement.
"
