import Game.Metadata
import Game.Levels.KnightsAndKnavesLemmas.L01_whydisjoint

import Game.Levels.KnightsAndKnavesLemmas.L02_Knight_NotKnave
import Game.Levels.KnightsAndKnavesLemmas.L03_Knave_NotKnight
import Game.Levels.KnightsAndKnavesLemmas.L04_NotKnave_Knight
import Game.Levels.KnightsAndKnavesLemmas.L05_NotKnight_Knave

World "KnightsAndKnavesLemmas"
Title "Knights and Knaves, lemmas"
Introduction 
"
This level will introduce the knights and knaves puzzle, detail the process of formalizing and representing it in Lean, and prove basic but important lemmas that will be used to solve puzzles in the next world.

The setting is an island in which its inhabitatnts satisfy the following properties:
- Every inhabitant of the island is either a knight or a knave. 
- 'Knights' always tell the truth and 'Knaves' always lie. 
The objective is to conclude who is a knight and who is a knave, based on the statements of several inhabitants. This will be done using logical reasoning. Every inhabitant will make at most one statement.

How should this be translated into Logic? Well, this is what the upcoming levels will focus on before transitioning to proving some important properties. 


Note that you can't be a Knight and a Knave at the same time, you can only be one or the other and not both. 
1. We can capture this in logic by saying that the two sets `Knight` and `Knave` are disjoint i.e there is no inhabitant that belongs to both at the same time. The notation for that is `Knight ∩ Knave = ∅` where `∅` is a set with no elements.
2. We can capture this in logic by saying that for any inhabitant say `A`, (`A` is a knight and is not a knave) or (`A` is a knave and is not a knight).
3. inductive type interpretation?  
variable (Inhabitant : Type)
#check (Sum Inhabitant Inhabitant
variable (A : Sum Knight Knave)
variable (B : Knight)
example : 2=2 := by sorry

Then, for any inhabitant of the island they are either a knight or a knave but not both. In other words, if they are a knight then they can't be a knave and if they are a knave they can't be a knight. This can be translated to : (x is a knight and x is not a knave) or (x is a knave and is not a knight). This can be simplified to just saying that: (x is a knight) or (x is a knave) conveying the same information. In the first case (x being a knight), we know the two sets are disjoint so x can't be a knave. Similarly for the second case. This simpler statement conveys the same information as the former which is more complicated, so it should ie be used instead.

-- don't show any formalism, just lay it out here then copy paste it to every level and formalise there.

The statement `x ∈ Knight` should be understand as 'x IS Knight' i.e 'x' always tells the truth. 
Similarly, the statement `x ∉ Knight` should be understand as 'x IS-NOT Knight'. What is `x` then? `x` has to be a knave.

The same reasoning applies to `x ∈ Knave`, `x ∉ Knave`.
Every mentioned here will be thoroughly formalized and explained in this world, and the paragraph in question in that level will be directly referenced. Every idea is left to be elaborated and formalised in the levels of this world.

"
