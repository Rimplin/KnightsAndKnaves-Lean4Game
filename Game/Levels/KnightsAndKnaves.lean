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

`P ↔ Q`  is defined as `(P → Q) ∧ (Q → P)`. But what does it mean? Let's construct its truth table and find out.(make it as the level itself??)

Remember,
$
\\begin{array}{|c c|c|} 
\\hline
P & Q & P → Q \\\\
\\hline
T & T & T \\\\
T & F & F \\\\
F & T & T \\\\
F & F & T \\\\
\\hline
\\end{array}
$

$
\\begin{array}{|c c|c|} 
\\hline
Q & P & Q → P \\\\
\\hline
T & T & T \\\\
T & F & F \\\\
F & T & T \\\\
F & F & T \\\\
\\hline
\\end{array}
$


The result is
$
\\begin{array}{|c c|c|} 
\\hline
P & Q & P → Q & Q → P & P → Q ∧ Q → P\\\\
\\hline
T & T & T & T & T \\\\
T & F & F & T & F \\\\
F & T & T & F & F \\\\
F & F & T & T & T \\\\
\\hline
\\end{array}

So, `P ↔ Q` is true when `P,Q` are true or `P,Q` are false, i.e when `P` and `Q` have the same truth value. Therefore, `P` and `Q` are equivalent from a truth value perspective regardless what the statement of `P` and of `Q` is.

To extract for example the forward direction `P → Q` from `h :P ↔ Q`, you do `h.mp`. This is a modus ponens version for `↔`. The reversed version `h.mpr` gives `Q → P`
$
"
