import Game.Metadata


World "LogicAlternative" 
Level 5

Title "Chain Of Implications" 

Introduction 
"
The `apply` tactic is much more useful when reasoning with multiplicaiton implications.

This is very clear if you attempt to solve this exercise by passing the premise to an implication, concluding the right hand side and then passing that to another implication and so on...
"
variable {P Q R S T : Prop}
Statement (hP: P) (PtoQ : P → Q) (QtoR : Q → R) (RtoS : R → S) (StoT : S → T) 
  : T := by

  {
    apply StoT 
    apply RtoS 
    apply QtoR
    apply PtoQ
    assumption
  }





Conclusion 
"
The alternative solution: 
```
exact  StoT (RtoS (QtoR (PtoQ hP)))
```
which is arguably less appealing and less readable.
"

/- Use these commands to add items to the game's inventory. -/
OnlyTactic apply assumption
--NewTactic 
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

