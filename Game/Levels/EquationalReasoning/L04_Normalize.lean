import Game.Metadata

World "EquationalReasoning" 
Level 4

Title "Normalize Equations" 

Introduction 
"In this level, we will learn about normalizing equations using the `norm_num` tactic.

`norm_num` is short for normalize numerical expressions like carrying out calculations and simplifying the expression.

We will also learn how to apply a tactic to an assumption instead of the goal.

We want to carry out the operation `4*4` in `h` and simplify the expression. `norm_num` does the job. `norm_num` would apply to the goal but want it to apply on `h`. Doing `norm_num at h` will do it.
"

Statement (h : x = 4*4)
  : x= 16 := by

  {
    norm_num at h
    Hint 
    "
    EXACTLY like the goal
    "
    exact h
  }

/-
example (h : x + 2 = 4)
  : x = 2 := by

  {
    norm_num at h 
    Hint "This should look familiar to a previous exercise. Now `h` looks exactly like the goal. Let Lean know that `h`'s type EXACTLY matches the goal. !!"
    Hint (hidden:=true) "Remember the `exact` tactic? Try `exact h`."
    exact h
  }

-/

Conclusion 
"
"

NewTactic norm_num

