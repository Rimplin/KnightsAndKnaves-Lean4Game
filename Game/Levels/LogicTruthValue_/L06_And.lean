import Game.Metadata

World "LogicTruthValue" 
Level 1

Title "" 

Introduction 
"
"

-- this is viable, the only issue is that the user has to explicitly go to the truth functional world, can this be forced somehow?? yes i can, by defining it and having the user user it. first make a level like this then make it easier for the user...
variable {emTruth : (P : Prop) → P = True ∨ P = False}
Statement : P = (P ∧ P) := by 
  --apply @iff_eq_eq.mpr P P 

  cases emTruth P
  · 
    rw [h] 
    rw [and_true] 
  · 
    rw [h]
    rw [and_false] 

Conclusion 
"
"
