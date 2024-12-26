import Game.Levels.KnightsAndKnaves.L01_IamKnave
import Game.Levels.KnightsAndKnaves.prob26
import Game.Levels.KnightsAndKnaves.IKnaveOrKnave
import Game.Levels.KnightsAndKnaves.prob33
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

Remember that if `A` were a knight, then `A`'s statement is true. As an implication:
```
A ∈ Knight → A ∈ Knave
```

If `A`'s statement were true, then `A` is telling the truth so `A` must be a knight. As an implication:
```
A ∈ Knave → A ∈ Knight
```

The two can be combined as 
```
stA : A ∈ Knight ↔ A ∈ Knave
```

Similarly, if `A` were a knave then `A`'s statement is false. As an implication:
```
A ∈ Knave → ¬(A ∈ Knave)
```

If `A`'s statement were false `A` must be a knave. As an implication:
```
¬(A ∈ Knave) → (A ∈ Knave)
```

Both can be combined as:
```
stAn : A ∈ Knave ↔ ¬(A ∈ Knave)
```

`P ↔ Q`  is defined as `(P → Q) ∧ (Q → P)`. 

Its truth table looks like the folowing:
$
\\begin{array}{|c c|c c|c|} 
\\hline
P & Q & P → Q & Q → P & P → Q ∧ Q → P\\\\
\\hline
T & T & T & T & T \\\\
\\hline
T & F & F & T & F \\\\
\\hline
F & T & T & F & F \\\\
\\hline
F & F & T & T & T \\\\
\\hline
\\end{array}
$

So, `P ↔ Q` is true when `P,Q` are true or `P,Q` are false, i.e when `P` and `Q` have the same truth value. Therefore, `P` and `Q` are equivalent from a truth value perspective regardless what the statement of `P` and of `Q` is.

The forward direction of `h :P ↔ Q` is `h.mp : P → Q`. 
The backward direction of `h :P ↔ Q` is `h.mpr : Q → P`. 
"
