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
