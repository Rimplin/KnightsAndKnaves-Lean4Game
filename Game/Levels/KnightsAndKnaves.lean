import Game.Levels.KnightsAndKnaves.L01_IamKnave
import Game.Levels.KnightsAndKnaves.prob26
import Game.Levels.KnightsAndKnaves.prob33
import Game.Levels.KnightsAndKnaves.prob28
import Game.Levels.KnightsAndKnaves.prob31
import Game.Levels.KnightsAndKnaves.prob32
World "KnightsAndKnaves"
Title "Knights And Knaves"
Introduction 
"
It is recommended to solve the problems in this world while in editor mode, though you have the choice not to.

give an example of formalization process i.e translating the statements to iff and the intuition behind that. the problem has already been presented in knights and knaves lemmas and the basic notleft_right etc.. lemmas

-- maybe provide a generic example in knights and knaves lemmas world where A : 'some statement' ......
-- generic
Say that `A` makes the statement `stA`. If `A ∈ Knight` then `stA` is true. If `stA` were true, then that means `A` told the truth, which means that `A ∈ Knight`. Translation : `A ∈ Knight → stA` etc.......
-- the first level
The process of representing knights and knaves problem will be discussed here using the first problem in this as an example.
Imagine the island has an inhabitant `A` which says the following statement,
A : 'I am a knave'
Remember that if `A` were a knight, then `A`'s statement is true. this can be translated to an implication: `A ∈ Knight → A ∈ Knave`
If `A`'s statement were true, then `A` is telling the truth so `A` must be a knight. `A ∈ Knave → A ∈ Knight`
The two can be combined as `A ∈ Knight ↔ A ∈ Knave`

"
