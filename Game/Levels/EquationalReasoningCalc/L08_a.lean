import Game.Metadata


World "EquationalReasoningCalc" 
Level 

Title "" 

Introduction 
"
"
variable {a b : ℕ}
Statement (h : (a + b)^2 = 9) (h' : a*b=2)
  : a^2 + 3*a*b + b^2 = 11 := by

  {
    calc 
      a^2 + 3*a*b + b^2 = (a^2 + 2*a*b + b^2) + a*b := by ring 
      _ = (a + b)^2 + a*b := by ring 
      _ = 9 + 2 := by rw [h,h']
      _ = 11 := by norm_num
  }





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

--NewTactic 
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

