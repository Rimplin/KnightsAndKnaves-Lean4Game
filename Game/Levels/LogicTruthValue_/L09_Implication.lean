import Game.Metadata

World "LogicTruthValue_" 
Level 4

Title "Implication, →" 
#check Function.mt
#check Function.mtr

#check and_imp
--variable {emTruth : (P : Prop) → P = True ∨ P = False}

#check iff_def
#check not_or_of_imp
#check true_iff
#check or_true
#check true_implies
 
Introduction 
"
In this level, we introduce the logical implication `→` connective.
Logical implication `P → Q` is made up of two components:
- The premise, which in this case is `P`
- The conclusion, which in this case is `Q`

# truth table
$
\\begin{array}{|c|c|c|} 
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

A statement `P → Q` is false when `P` is true and `Q` false, it's true otherwise.
This is because this is the only case where the meaning of `P → Q` is violated i.e we have that `P` is true so `Q` is supposed to be true as well but its not.

We know `P` (i.e `P = True`) , and we know `P → Q` (i.e `P = True → Q = True`). We can now conclude `Q` (i.e `Q = True`).

What logical implication does is that it takes evidence or proof for `P` and transforms it returning a proof of `Q`.
The truth of `P` IMPLIES the truth of `Q`. A proof of `P` IMPLIES a proof of `Q`.

In other words, it acts like a function. If you give `P → Q` a proof of `P`, you get a proof of `Q`.
"
Statement {P Q : Prop}  (p : P) (ptoq: P → Q) : Q := by 
  exact ptoq p

Conclusion 
"
In this level, you will learn how to deal with an implication as the goal you have to prove.
"
-- This is what is called an inference rule. It has two assumptions, `p : P` , `ptoq : P → Q` and the conclusion `Q`. It is an inference rule because we 'infer' a certain conclusion from assumptions or already established theorems.

#check imp_iff_not_or
NewDefinition imp 
