import Game.Metadata


World "LogicAlternative" 
Level 6

Title "" 

Introduction 
"
"


  
Statement (forward: (P → Q))
  : (¬Q → ¬P) := by
  {
    intro nq
    intro np 
    apply nq 
    apply forward
    assumption
  }





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

--NewTactic 
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

