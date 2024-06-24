import Game.Metadata


World "LogicAlternative" 
Level 4

Title "`apply` tactic" 

Introduction 
"
The `apply` tactic takes an implication as its argument where the conclusion of the implication matches the goal.
Here is how `apply` 'thinks', and how it transforms the proof state:
Since we can conclude the conclusion of the implication which is also our goal from its premise, our new goal becomes the premise. In a sense, the `apply` tactic sets up modus ponens for you and the missing piece is proving the premise of the implication

remember the X Y problem

"

variable {P Q : Prop}
Statement  (hP : P) (ptoq: P → Q)
  : Q := by

  {
    apply ptoq
    assumption
  }





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/
/-- The apply tactic takes a proof of a general statement or implication, tries to match the conclusion with the current goal,
and leaves the hypotheses, if any, as new goals. If the given proof matches the goal exactly (modulo definitional equality),
you can use the exact tactic instead of apply. So, all of these work: -/
TacticDoc apply 
NewTactic apply
OnlyTactic apply assumption
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

