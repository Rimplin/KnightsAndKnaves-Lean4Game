import Game.Metadata


World "Logic" 
Level 7

Title "Disjunctive Syllogism" 

Introduction 
"

"
variable {P Q : Prop}
Statement (h : P ∨ Q) (np : ¬P)
  : Q := by

  {
   cases h 
   have := np h_1  

  }





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

--NewTactic rw rfl
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

