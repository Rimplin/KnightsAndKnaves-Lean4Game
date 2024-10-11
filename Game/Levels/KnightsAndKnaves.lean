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
It is recommended to solve the problems in this world while in editor mode, though you have the choice not to. Levels with longer solutions will force editor mode.

Suppose the island has an inhabitant `A` which says the following statement,
A : 'I am a knave'
Remember that if `A` were a knight, then `A`'s statement is true. this can be translated to an implication: `A ∈ Knight → A ∈ Knave`
If `A`'s statement were true, then `A` is telling the truth so `A` must be a knight. `A ∈ Knave → A ∈ Knight`
The two can be combined as `A ∈ Knight ↔ A ∈ Knave`
"
