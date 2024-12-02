import Game.Metadata

World "LogicTruthValue_" 
Level 5

Title "" 

Introduction 
"
The goal, translated to normal english is: 'If P is true, then P is true'.

To prove such a goal, we need to assume that `P` is true. Then, we have to prove that `P` is true.

To do this, we need to assume the premise i.e introduce it to our assumptions. We can do this using `intro`.

After that , we have to prove the consequent.
"

Statement {P :Prop}
  : P → P  := by
  {
    intro hP
    exact hP
  }

Conclusion 
"
use `intro name` to give the introduced hypothesis a name
"
