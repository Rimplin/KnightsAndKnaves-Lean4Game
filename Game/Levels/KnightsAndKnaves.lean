import Game.Levels.KnightsAndKnaves.L01_IamKnave
import Game.Levels.KnightsAndKnaves.prob26
import Game.Levels.KnightsAndKnaves.IKnaveOrKnave
import Game.Levels.KnightsAndKnaves.prob33
import Game.Levels.KnightsAndKnaves.prob28
import Game.Levels.KnightsAndKnaves.prob31
import Game.Levels.KnightsAndKnaves.prob32
World "KnightsAndKnaves"
Title "Knights And Knaves"
--'stA' stands for 'statement of A'
/-
In a proof state, this would look like:
```
A ∈ Knave
```
-/

Introduction 
"
Suppose the island has an inhabitant `A` which says the following statement,
```
A says 'I am a knave'
```

Formally, the statement 'I am a knave' is `A ∈ Knave`.

Remember that if `A` were a knight, then `A`'s statement is true. This can be translated to an implication: `A ∈ Knight → A ∈ Knave`

If `A`'s statement were true, then `A` is telling the truth so `A` must be a knight. `A ∈ Knave → A ∈ Knight`

The two can be combined as `A ∈ Knight ↔ A ∈ Knave`
"
