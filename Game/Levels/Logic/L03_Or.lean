import Game.Metadata


World "Logic" 
Level 3 

Title "Or" 

Introduction 
"
Or introduction
"

Statement (hP : P) (hQ : Q) 
  : P ∨ Q  := by

  {
    exact Or.inl hP
  }





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

NewTactic Or.inl
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

