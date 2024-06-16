import Game.Metadata


World "BasicAlgebra" 
Level 3

Title "Substituting Variables By Their Values" 

Introduction "We will learn how to substitute the value of a variable.

This can be done using the tactic `rw` (short for rewrite).

`rw` takes a term of type `A=B` and replaces all the `A`s in the goal with `B`s"

Statement (h : x = 3) (g: y = 6) (i : z=10) : x + x = y := by
  Hint "Do `rw [{h}]` or `rw [{g}]` and observe what happens."
  Branch
    rw [g]
    Hint "You should use `{h}` now."
    rw [h]
  rw [h]
  Hint "You should use `{g}` now."
  rw [g]





Conclusion 
"
Our goal is now `3 + 3 = 6` which Lean knows to be true because it's a direct consequence of the definition of the natural numbers. 

Notice we didn't use the fact `i` which is that `z=10`. You should ignore any assumptions you think are irrelevant to proving the goal.

"

/- Use these commands to add items to the game's inventory. -/

NewTactic rw 
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

