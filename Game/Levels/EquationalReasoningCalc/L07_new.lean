import Game.Metadata


World "EquationalReasoningCalc" 
Level 7

Title "" 

Introduction 
"
We need to get rid of `y` reaching a number, in this case `9`. We know that `y` is equal to some expression involving `x` and we know what number `x` is, so this seems like the way to do it. 
"

Statement 
  :  := by

  {

  }

example (x y : ℤ) (h1 : x = 3) (h2 : y = 4 * x - 3) : y = 9 := by
calc
  y   = 4 * x - 3 := by rw [h2]
  _ = 4 * 3 - 3:= by rw [h1]
  _ = 12 - 3   := by norm_num
  _ = 9        := by norm_num

Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

--NewTactic 
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

