import Game.Metadata


World "BasicAlgebra" 
Level 2

Title "Introd" 

Introduction "`h` is a proof of `x = 2`. Our goal is to prove that `x = 2`. To do this, we should let Lean know that we have a term that 'exactly' matches that goal. 

Using `exact h` will accomplish that."

variable (x : ℕ )
Statement (h : x=2)
  : x=2 := by

  {
    exact h
  }





Conclusion ""

/- Use these commands to add items to the game's inventory. -/


/-
Testing rfl description1
-/
--TacticDoc rfl


/--
## Overview
Having h : P and P as your goal, exact h will close the goal. exact h asserts that h is exactly whats needed to prove the goal which makes sense because h is a proof of P.(It doesn't matter what P is)
-/
TacticDoc exact
NewTactic exact
-- NewLemma Nat.add_comm Nat.add_assoc

DefinitionDoc Nat as "ℕ"  
NewDefinition Nat 

