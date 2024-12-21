import Game.Metadata

Introduction 
"
For your convenience, the contradiction tactic will be unlocked after this level so you don't have to do the same steps when there are contradictory assumptions.

False.elim eliminates false and produces an object of any type you want!!!

$\\displaystyle {\\frac {P\\lor Q,\\neg P}{\\therefore Q}}$

## Principle of explosion
Moreover, `False` has no introduction rule , so the reasoning described above is the only way to obtain an object of type `False`. 
"

/-
we have proved a statement that is not true. Since we proved it, now it's also true? Let's denote this proposition as `Q`. So we have `Q ∧ ¬Q`. What does the truth table for this expression look like for any proposition `R`?
$
\\begin{array}{|c|c|} 
\\hline
R & ¬R & R ∧ ¬R \\\\
\\hline
T & F & F \\\\
F & T & F \\\\
\\hline
\\end{array}
$
This statement is always false regardless of the truth values of `R` but we were able to prove such a statement. we can write `R ∧ ¬R = False` from this truth table.

The system you are working with quickly becomes trivial and loses its value. If you're objective is to reach truth, then there is nothing to do here because everything is true. There is nothing to study or investigate, its all true!

Proving `False` means deriving a contradiction.

A contradiction is when `p` and `¬p` are both true. `False ≠ True` is always true regardless of proof state, but in this state we also have `False = True` giving us a contradiction. Notice that even our starting point was of contradiction, where we had `p = True` and `p = False` i.e `¬p = True`.
-/

#check imp_false
#check eq_false
#check eq_false'
#check implies_true
#check true_implies
#check true_imp_iff
#check false_implies
#check true_iff
#check false_iff
#check iff_false
#check Or.elim
#check not_not

Conclusion 
"
We have proven that `P ∧ ¬P → Q` for any proposition `Q`. since `P ∧ ¬P` is always false, then the implication proved becomes `False → Q`.

There are more examples of contradictions like
¬(P ∨ ¬P)

$
\\begin{array}{|c c|c|} 
\\hline
P & ¬P & P ∨ ¬P & ¬(P ∨ ¬P) \\\\
\\hline
T & F & T & F \\\\
F & T & T & F \\\\
\\hline
\\end{array}
$
"
