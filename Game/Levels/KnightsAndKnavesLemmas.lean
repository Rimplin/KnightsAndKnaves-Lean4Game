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
This introduction will introduce the knights and knaves puzzle, and prove basic but important lemmas that will be used to solve the actual puzzles in the next world.

-- talk about sets here because set theory world is before this.
-- introduce the sets Knight , Knave
Let `Knight` be the set of inhabitants that are knights, i.e always tell the truth.
Let `Knave` be the set of inhabitants that are knaves, i.e always lies.
In a proof state, this would look like:
```
Inhabitant : Type
Knight : Set Inhabitant
Knave : Set Inhabitant
```
The statement `x ∈ Knight` should be understand as 'x IS Knight' i.e 'x' always tells the truth. 
Similarly, the statement `x ∉ Knight` should be understand as 'x IS-NOT Knight'. What is `x` then? `x` has to be a knave.

The same reasoning applies to `x ∈ Knave`, `x ∉ Knave` and to any set.

The setting is an island in which its inhabitatnts satisfy the following properties:
- Every inhabitant of the island is either a knight or a knave which is expressed as : A ∈ Knight ∨ A ∈ Knave.
- 'Knights' always tell the truth and 'Knaves' always lie. Clearly, no inhabitant can be both a knight and a knave. So the intersection of bothe sets is empty. Knight ∩ Knave = ∅. The two sets Knight Knave are disjoint.
The objective is to conclude who is a knight and who is a knave, based on the statements of several inhabitants. This will be done using logical reasoning. Every inhabitant will make at most one statement.

How should this be translated into Logic? Well, this is what the upcoming levels will focus on before transitioning to proving some important properties. 

-- don't show any formalism, just lay it out here then copy paste it to every level and formalise there.


Every mentioned here will be thoroughly formalized and explained in this world, and the paragraph in question in that level will be directly referenced. Every idea is left to be elaborated and formalised in the levels of this world.

"
