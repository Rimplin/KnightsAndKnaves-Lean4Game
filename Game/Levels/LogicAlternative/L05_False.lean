import Game.Metadata


World "LogicAlternative" 
Level 5

Title "" 

Introduction 
"
"
variable {P Q : Prop}
Statement (h : P) (hn : ¬ P)
  : False := by

  {
   apply hn 
   assumption
  }





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

--NewTactic 
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

