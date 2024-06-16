import Game.Metadata


World "BasicAlgebra" 
Level 5 

Title "some title" 

Introduction 
"
Here, we introduce a multiplication cancellation tactic.

To be able to achieve this, we need to rewrite `16` in `h` as `4 * 4` to be able to cancel the `4` on both sides of the equation , proving `y=4`. 

But first, we need to construct an object of type `16 = 4 * 4` (a proof) and add it to our assumptions.

This is exactly what `have` does

The syntax is 
`have name-of-object : type := by ...` where `...` is the proof.

The type here is `16 = 4 * 4`, you can pick anything as `name-of-object` like `helper`. For the proof, we need to carry out the calculation of `4 * 4` and as in the previous level, the tactic for that is `norm_num`. Typing that as the proof will work.

Alternative syntax:
`have name := ........`
"

variable [IsLeftCancelMul ℕ] 
Statement (h : 4*y=16) : y = 4 := by{
  Hint (hidden := true) (strict := true) "Try `have helper : 16=4*4 := by norm_num`" 
  have helper : 16=4*4 := by norm_num 
  Hint "Now we want to replace the `16` in `{helper}` with `4 * 4`"
  Hint (hidden := true) "`rw [{helper}] at h`" 
  rw [helper] at h 
  Hint "
  Now that we have `4` on both sides, we want to cancel this `4`

  This is possible using the theorem `Nat.mul_left_cancel` which has the following type :
  ```
  mul_left_cancel(a✝ : a * b = a * c) :
  b = c

  ```
  `mul_left_cancel` takes one argument which is the equation you are working with, then cancels `a` from both sides giving a proof of `b=c`. This is exactly what we want to prove the goal.

  "
  Hint (hidden:=true) "
  Notice that `mul_left_cancel h` has type `y = 4`. So, `exact mul_left_cancel h` will do it."
  exact mul_left_cancel h
}






Conclusion ""

/- Use these commands to add items to the game's inventory. -/

/--

-/
TacticDoc «have»
NewTactic «have»

/- Focus on the type of `four_pos : 0 < 4`. The rest is just arguments that if you don't pass to Lean, Lean will deduce automatically. You can always learn what they mean by refering to the mathlib documentation -/
--TheoremDoc four_pos as "four_pos" in ">0"

/-

  `Nat.mul_left_cancel` takes two arguments, the first `np` is a proof that what you are cancelling from both sides of the equation is positive, and the second `h` is the equation itself. Its type is the equation `h` with `n` cancelled from both sides.

  In our cases, we want a proof that `4` is positive which is `four_pos : 0 < 4` and the equation we are working with which is `h`
-/
/-- some info -/
TheoremDoc mul_left_cancel as "mul_left_cancel" in "*"
NewTheorem mul_left_cancel 
-- NewDefinition Nat Add Eq
