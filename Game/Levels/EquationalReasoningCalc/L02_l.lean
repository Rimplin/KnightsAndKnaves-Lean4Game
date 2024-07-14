import Game.Metadata


World "EquationalReasoningCalc" 
Level 2

Title "" 

Introduction 
"
"

Statement (h : x + 2 = 4)
  : x = 2 := by{
    calc
      x = (x + 2) - 2:= by sorry 
      _ = 4 - 2 := by sorry
      _ = 2 := by sorry
  }
/-

    calc
      x = (x + 2) - 2:= by ring! 
      _ = 4 - 2 := by rw [h]
      _ = 2 := by norm_num
-/



Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

--NewTactic 
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

