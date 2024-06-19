import Game.Metadata


World "EquationalReasoning" 
Level 3

Title "Substituting Variables By Their Values" 

Introduction "We will learn how to substitute a variable with its value, for example how to substitiute `x` by `2` if we know that `x=2`.

This can be done using the tactic `rw` (short for rewrite).

`rw` takes a term of type `A=B` and replaces all the `A`s in the goal with `B`s.
So `rw [h]` where `h : x=3` will replace all the `x`s of the goal with `3`.
"


Statement (h : x = 3) (g: y = 6) (i : z=10) : x + x = y := by

  Hint "Do `rw [{h}]` or `rw [{g}]` and observe what happens."
  Branch
    rw [g]
    Hint "You should use `{h}` now."
    Hint (hidden:= true) "`rw [h]`"
    rw [h]
  rw [h]
  Hint "You should use `{g}` now."
  Hint (hidden:= true) "`rw [g]`"
  rw [g]





Conclusion 
"
Our goal is now `3 + 3 = 6` which Lean knows to be true because it's a direct consequence of the definition of the natural numbers. So, there's nothing left to do. 

Notice we didn't use the fact `i: z=10` which is that `z=10`. This will not be the case for the majority of exercises, you will need to use all the assumptions you have (explicitly or implicity).

Another solution:
```
rw [h,g]
```
instead of 
```
rw [h]
rw [g]
```

"

/- Use these commands to add items to the game's inventory. -/

NewTactic rw 
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

