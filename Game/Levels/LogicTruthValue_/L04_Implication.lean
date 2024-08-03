import Game.Metadata


World "LogicTruthValue_" 
Level 4

Title "Implication, →" 

Introduction 
"
Logical implication `P → Q` is made up of two components:
- The premise, which in this case is `P`
- The conclusion, which in this case is `Q`

What logical implication does is that it takes evidence or proof for `P` and transforms it returning a proof of `Q`.
# truth table
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

A statement `P → Q` is false when `P` is true and `Q` false, it's true otherwise. Since the statement expresses that if `P` is true then `Q` is true, then should make intuitive sense. This utterance is not violated in other cases so the statement is true in those cases.

Representing this rule symbolically:
$\\displaystyle {\\frac {P\\rightarrow Q, P}{\\therefore Q}}$

This is what this format means in general:
$\\displaystyle {\\frac {Premises}{Conclusion}}$

We know `P` (i.e `P = True`) , and we know `P → Q` (i.e `P = True → Q = True`). We can now conclude `Q` (i.e `Q = True`).
"
variable {P Q : Prop}
-- redundant ...
--TheoremDoc modus_ponens as "modus_ponens" in "logic"
--previously without =True
Statement  (p : P=True) (ptoq: (P=True) → (Q=True))
  : Q=True := by
  {
    exact ptoq p
  }





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

--TheoremDoc mul_left_cancel as "mul_left_cancel" in "*"
--NewTheorem mul_left_cancel 

/- asdf -/
--TheoremDoc modus_ponens as "modus_ponens" in "logic"
--NewTheorem modus_ponens 

/- some info -/
--TheoremDoc mul_left_cancel as "mul_left_cancel" in "*"
--NewTheorem mul_left_cancel 
-- NewDefinition Nat Add Eq
--NewTheorem
/-- no lean docstring avaialble

# truth table
$
\begin{array}{|c c|c|} 
\hline
P & Q & P → Q \\
\hline
T & T & T \\
T & F & F \\\\
F & T & T \\\\
F & F & T \\\\
\hline
\end{array}
$
-/
DefinitionDoc imp as "→"
NewDefinition imp 
