import Game.Metadata


World "EquationalReasoningCalc" 
Level 3

Title "" 

Introduction 
"
"

Statement (h : 4*y=16) : y = 4 := by{
  calc 
    y = (4*y)/4 := by sorry
    _ = 16/4 := by sorry
    _ = 4 := by sorry
}
/-
  calc 
    y = (4*y)/4 := by omega
    _ = 16/4 := by rw [h]
    _ = 4 := by norm_num/ring
-/

Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

--NewTactic 
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

