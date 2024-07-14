import Game.Metadata


World "EquationalReasoningCalc" 
Level 1

Title "" 

Introduction 
"
Remember level 3 in equational reasoning.

# `calc`

# `sorry`?
You are sorry you don't know the proof and Lean accepts that and closes the goal. Note: this is very dangerous because you might have Lean admit something that is false, which is not a good idea.
"

Statement (h : x = 3) (g: y = 6) (i : z=10) : x + x = y := by
{
  Template
  calc 
  x+x = 3+3 := by sorry
    _ = 6 := by sorry
    _ = y := by sorry
      
}




Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

NewTactic «calc»  
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

