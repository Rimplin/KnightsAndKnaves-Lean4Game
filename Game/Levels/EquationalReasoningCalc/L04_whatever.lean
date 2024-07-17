import Game.Metadata


World "EquationalReasoningCalc" 
Level 4

Title "" 

Introduction 
"
This is the last level you have seen before, the rest will be new.
"

Statement {y : ℚ } (h : 4*y=16) : y = 4 := by{
  Template
    calc 
      y = (4*y)/4 := by sorry
      _ = 16/4 := by sorry
      _ = 4 := by sorry
}

/-
  calc 
    y = (4*y)/4 := by ring
    _ = 16/4 := by rw [h]
    _ = 4 := by norm_num/ring
-/

Conclusion 
"
"

-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
