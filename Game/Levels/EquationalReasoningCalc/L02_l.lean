import Game.Metadata


World "EquationalReasoningCalc" 
Level 2

Title "" 

Introduction 
"
Good luck!
"

Statement {x : ℤ} (h : x + 2 = 4)
  : x = 2 := by{

  Template
    calc 
      x = x + 2 - 2 := by sorry 
      _ = 4 - 2 := by sorry
      _ = 2 := by sorry
  }
/-

    calc
      x = (x + 2) - 2:= by ring 
      _ = 4 - 2 := by rw [h]
      _ = 2 := by norm_num
-/

Conclusion 
"
Notice that the pattern for this `calc` is rearrange variables, rewrite, rewrite. The next problem will have the same pattern in addition to requiring a calculation at the end.
"

NewTactic ring
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

