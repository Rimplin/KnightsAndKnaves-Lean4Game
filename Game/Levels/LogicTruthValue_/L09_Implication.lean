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

What logical implication does is that it takes evidence or proof for `P` and transforms it returning a proof of `Q`.
The truth of `P` IMPLIES the truth of `Q`. A proof of `P` IMPLIES a proof of `Q`.

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
"
Statement  (p : P) (ptoq: P → Q) : Q := by 
  exact ptoq p 

Conclusion 
"
This is what is called an inference rule. It has two assumptions, `p : P` , `ptoq : P → Q` and the conclusion `Q`. It is an inference rule because we 'infer' a certain conclusion from assumptions or already established theorems.
Usually presented in this format:
"

NewDefinition imp 
