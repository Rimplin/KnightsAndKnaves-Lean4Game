import Game.Metadata

variable (P Q R : Prop)

World "Logic"
Level 1

Title "Intro "

Introduction 
" Notice that the objects of interest are now of type `Prop` (i.e proposition). A proposition is a statement/assertion that can take only one of two values, either true or false. Having `hP:P` means that we have a proof of `P`, and therefore you can think about this as `P` being true.

`hP` 'exactly' matches the goal. `hP` is 'exactly' what you need to close the goal. This is to emphasize that for the tactic `exact h`, the type of h doesn't matter."

Statement (hP: P) (hQ: Q) (hR : R)
  : P := by
  {
   Hint (hidden := true) "Type `exact hP`!"
   exact hP
  }





Conclusion "Notice that `hQ` and `hR` were not used. We couldn't use them in any case because `Q` and `R` are not related to `P`. In the next levels, we will discuss how to construct new propositions from old ones which would in a sense depend on the old ones. "

/- Use these commands to add items to the game's inventory. -/



/-
is it working???
## Overview
Having h : P and P as your goal, exact h will close the goal. exact h asserts that h is exactly whats needed to prove the goal which makes sense because h is a proof of P.(It doesn't matter what P is)
-/
/- TacticDoc «sorry»
 NewTactic «sorry» 
 NewLemma Nat.add_comm Nat.add_assoc
-/
NewDefinition 
