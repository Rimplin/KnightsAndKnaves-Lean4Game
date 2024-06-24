import Game.Metadata


World "LogicAlternative" 
Level 1

Title "`assumption` tactic" 

Introduction 
"
"

variable {P Q : Prop}
Statement (hP: P) (hQ: Q) (hR : R)
  : P := by
  {
    assumption
   --Hint (hidden := true) "Type `exact hP`!"
  }





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

NewTactic assumption
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

