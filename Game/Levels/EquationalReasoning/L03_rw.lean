import Game.Metadata


World "EquationalReasoning" 
Level 3

Title "Substituting Variables By Their Values" 

--By default, rw uses an equation in the forward direction, matching the left-hand side of the equation with an occurrence of that in the goal, and replaces it with the right-hand side. 
--
--# mention reverse direction??
--The notation ←t can be used to instruct the tactic to use the equality t in the reverse direction.
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

/-
definitional equality....

which Lean knows to be true because it's a direct consequence of the definition of the natural numbers. So, there's nothing left to do. Providing a bit more detail, this is what is called 'definitional equality', i.e two things are equal due to the way they are defined (these types of goals can be closed using `rfl`). But you didn't have to use `rfl` here. `rw` actually tries `rfl` after the substitution, because its a common pattern. Another version `rewrite` doesn't, but it is not made available in this game and is mentioned for your information.

Notice we didn't use the fact `i: z=10` which is that `z=10`. This will not be the case for the majority of exercises, you will need to use all the assumptions you have (explicitly or implicity).
-/
Conclusion 
"
Our goal is now `3 + 3 = 6`. The `rw` tactic implicitly executes `rfl` after doing the rewrite which proved the goal here. 


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


NewTactic rw 
