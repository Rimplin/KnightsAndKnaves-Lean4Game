import Game.Metadata


World "EquationalReasoning"
Level 6

Title "Final"

Introduction
"
A similar problem to the previous one.
"

variable {x y : ℚ }

example  (h : 3*x - 2*y = 12) (k : y = 3) : x = 6 := by {
  calc  
   x = 3*x -2*y -2*x +2*y := by ring
   _ = 12 - 2*x + 2*3 := by rw[h,k]
   _ = 18-2*x := by ring 
   _ = 18 -(3*x -2*y)/(3/2) - 4*y/3 := by ring
   _ = 18 - (12)/(3/2) - 4*3/3 := by rw [h,k]
   _ = 6 := by ring
}

variable {x y : ℤ}
example  (h : 3*x - 2*y = 12) (k : y = 3) : x = 6 := by {
 rw [k] at h
 have helper : 3*x = 12 + 6:= by exact eq_add_of_add_neg_eq h

 norm_num at helper

 have helper2 :(18:ℤ)=3*6:= by norm_num
 rw [helper2] at helper
 exact mul_left_cancel₀ three_ne_zero helper
}

Statement  (h : 3*x - 2*y = 12) (k : y = 3) : x = 6 := by {
  --calc
  --  x = 3*x -2*y -2*x +2*y := by polyrith
  --  _ =

 Hint "First start by substitute the value of `y` in `h`"
 rw [k] at h
 Hint "Now simplify `h`"
 norm_num at h
 Hint "
 We need to isolate `3*x` on the left side of the equation. You can do this using the `eq_add_of_add_neg_eq` theorem which is of type:
 ```
eq_add_of_add_neg_eq (h : a + -c = b) : a = b + c
 ```
 We can use this theorem with the `have` tactic to construct a term of type `3 * x = 12 + 6`
 "
 have helper : 3*x = 12 + 6:= by exact eq_add_of_add_neg_eq h
 Hint "Simplify `{helper}`"
 norm_num at helper
 Hint "Now, like the previous exercise, you need to construct a term of type `(18:ℤ)=3*6`"
 have helper2 :(18:ℤ)=3*6:= by norm_num
 
 Hint "Replace the `18` with 3*6"
 rw [helper2] at helper
-- exact IsLeftCancelMul.mul_left_cancel 3 x 6 helper
-- exact mul_left_cancel ℚ IsLeftCancelMul.mul_left_cancel ℚ helper
 --exact (IsLeftCancelMul.mul_left_cancel 3 x 6) helper
 Hint 
 "
 Cancel `3` from both sides and your done

 Remember `mul_left_cancel₀`
 "
 exact mul_left_cancel₀ three_ne_zero helper

 --rw [exppp] at helper2  -- works fine
 --rw [exppp] at helper -- gives a tactic rewrite failed
 --rw [exppp] at current

 --rw [helper2] at helper

 --have current : 3 * x = 18 := helper
 --have current : 18 = 3 * x := by exact Eq.symm helper
 --rw [exppp] at current
 --rw [helper2] at current

 --rw [←helper] at helper2

 --rw [helperr] at current
 --rw [helperr] at helper


/-
Statement (h : 4*y=16) : y = 4 := by{
  Hint (hidden := true) (strict := true) "Try `have helper : 16=4*4 := by norm_num`"
  have helper : 16=4*4 := by norm_num
  Hint "Now we want to replace the `16` in `{helper}` with `4 * 4`"
  Hint (hidden := true) "`rw [{helper}] at h`"
  rw [helper] at h

-/
 --etc, nice!!!!
 --have helper: 3 * x = 12 + 6 := by omega
---- norm_num at helper
 --have helper2 : x = 6 := by omega
 --exact helper2

 -- etc...., does this look familiar?
 --have helper : (3*x - 6) + 6 =12 +6:= by rw [h]
 --simp? at helper
 --ring_nf at helper
 --norm_num at helper
 --linear_combination
 --have helper : (3*x - 6) + 6 =12 +6:= by linear_combination h + 6
 --norm_num at helper
  --have helper : 16=4*4 := by norm_num
 --
 -- --polyrith
--  bv_omega
  --aesop
  --hint
  --simp at h
  --linarith
}

Conclusion
"
"

NewTheorem eq_add_of_add_neg_eq three_ne_zero mul_left_cancel₀
