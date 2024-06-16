import Game.Metadata


World "BasicAlgebra" 
Level 4

Title "Normalize Equations" 

Introduction 
"In this level, we will learn about normalizing equations using the `norm_num` tactic.

`norm_num` is short for normalize numerical expressions like carrying out calculations and simplifying the expression.

We will also learn how to apply a tactic to an assumption instead of the goal.

We want to use `norm_num` on h, so simply write `norm_num at h`.
"

Statement (h : x + 2 = 4)
  : x = 2 := by

  {
    norm_num at h 
    Hint "Now `h` looks exactly like the goal"
    exact h
  }





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

NewTactic norm_num
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

