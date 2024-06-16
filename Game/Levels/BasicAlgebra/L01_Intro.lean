import Game.Metadata


World "BasicAlgebra" 
Level 1

Title "A Number Equals Itself" 

Introduction "In this exercise, we will prove `2 = 2`

`rfl` will do the job."

Statement 
  : 2 = 2 := by

  {
    rfl
  }





Conclusion "`rfl` means reflexivity, which is the property that for any number `a`, `a = a`"

/- Use these commands to add items to the game's inventory. -/

NewTactic rfl
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

