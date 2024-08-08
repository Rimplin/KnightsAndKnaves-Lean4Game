import Game.Metadata

/--
Unfoldable:
unfold Not at ...
¬P is P → False
-/
DefinitionDoc Not as "¬"

/--
`rfl` is short for reflexivity, which is the property that for any number `a`, `a = a`.

The `rfl` tactic will close all goals of the form `X=X`, regardless of what `X` is.

In fact, `rfl` is not a tactic but syntactic sugar for `exact rfl`. `rfl` is of type `a = a` for any `a`.
## examples
```
x - 7 = x - 7
```
`rfl` will close this goal.
-/
TacticDoc rfl

/--
testing stuff, does importing work?!?!?!?!
-/
TacticDoc left



/--
[[mathlib_doc]]
-/
TacticDoc «have»



/--
## Overview
Having h : P and P as your goal, exact h will close the goal. exact h asserts that h is exactly whats needed to prove the goal which makes sense because h is a proof of P.(It doesn't matter what P is)
-/
TacticDoc exact


/-- 
Normalize numerical expressions. Supports the operations `+` `-` `*` `/` `⁻¹` `^` and `%`
over numerical types such as `ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ`.

-/
TacticDoc norm_num

/--

# Truth table
The truth table of a logical connective illustrates the rule for that logical connective , i.e the truth value of the compound statement depending on the truth value of the propositions it connects.
The following truth table illustrates this for the previously discussed `∧` connective.
`T` stands for true
`F` stands for false
$
\begin{array}{|c c|c|} 
\hline
P & Q & P ∧ Q \\
\hline
T & T & T \\
T & F & F \\
F & T & F \\
F & F & F \\
\hline
\end{array}
$
Notice that `P ∧ Q` is true when both `P` is true and `Q` is true, being false otherwise.
-/
TheoremDoc And as "And" in "Logic"
