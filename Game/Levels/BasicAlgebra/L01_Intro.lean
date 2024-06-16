import Game.Metadata


World "BasicAlgebra" 
Level 1

Title "A Number Equals Itself" 

Introduction "In this exercise, we will prove `2 = 2`

`rfl` will do the job.

`rfl` is short for reflexivity, which is the property that for any number `a`, `a = a`

`rfl` also applies more generally, `rfl` will close any goal of the form `A=B` where `A`,`B` are identical.
"

Statement 
  : 2 = 2 := by

  {
    rfl
  }





--Conclusion "`rfl` means reflexivity, which is the property that for any number `a`, `a = a`"

/- Use these commands to add items to the game's inventory. -/

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
NewTactic rfl
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

