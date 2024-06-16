import Game.Metadata


World "BasicAlgebra" 
Level 5 

Title "some title" 

Introduction 
"
Here, we introduce a multiplication cancellation tactic.

To be able to achieve this we need to rewrite `16` in `h` as `4 * 4` to be able to cancel the `4` on both sides of the equation , proving `y=4`. 

But first, we need to construct an object of type `16 = 4 * 4` (a proof) and add it to our assumptions.

This is exactly what `have` does

The syntax is 
`have name-of-object : type := by ...` where `...` is the proof.

The type here is `16 = 4 * 4`, you can pick anything as `name-of-object` like `helper`. For the proof, we need to carry out the calculation of `4 * 4` and as in the previous level, the tactic for that is `norm_num`. Typing that as the proof will work.

"

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
   Nat.mul_left_cancel  (np : 0 < n) (h : n * m = n * k) :
m = k
  ```
  where `n,m,k` are natural numbers.

  `Nat.mul_left_cancel` takes two arguments, the first `np` is a proof that what you are cancelling from both sides of the equation is positive, and the second `h` is the equation itself. Its type is the equation `h` with `n` cancelled from both sides.

  In our cases, we want a proof that `4` is positive which is `four_pos : 0 < 4` and the equation we are working with which is `h`
  "
  Hint (hidden:=true) "
  Notice that `Nat.mul_left_cancel four_pos h` has type `y = 4`. So, `exact Nat.mul_left_cancel four_pos h` will do it."
  exact Nat.mul_left_cancel four_pos h
}






Conclusion ""

/- Use these commands to add items to the game's inventory. -/

NewTactic «have»

TheoremDoc four_pos as "four_pos" in ">0"
TheoremDoc zero_lt_four as "zero_lt_four" in ">0"

TheoremDoc zero_lt_four' as "zero_lt_four'" in ">0"
TheoremDoc Nat.mul_left_cancel as "Nat.mul_left_cancel" in "*"
NewTheorem Nat.mul_left_cancel four_pos zero_lt_four zero_lt_four'
-- NewDefinition Nat Add Eq
