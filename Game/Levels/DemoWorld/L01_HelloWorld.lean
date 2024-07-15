import Game.Metadata
open Nat
--open Group

example (a b c d e f g : ℝ) (h : a + b + c = d - e + f - g) : a/2 + b/2 + c/2 = d/2 - e/2 + f/2 - g/2 := by

  field_simp
  exact h
 --   rw ← add_assoc,
 --   rw h,
 --   ring,
 -- end

example (y : ℕ) (h:4*y=16) : y=4 := by
  --hint
  --omega
  linarith

example (y : ℕ) (h:3*y=12) : y=4 := by
  --omega
  apply Nat.mul_left_cancel three_pos
  rw [h]
  norm_num


example (h : 3*y + 2*x = 16) (k : x = 2) : y = 4 := by
  rw [k] at h
  norm_num at h
  exact Nat.mul_left_cancel three_pos h

  --simp only [reduceMul] at h

  --rw [Nat.add_comm] at h
  --norm_num at h

  --repeat rw [succ.injEq] at h

  -- h : 3*y=12
  --have helper : 12 = 3*4 := by norm_num
  --rw [helper] at h
  --have tg0 : 0<3 := by simp
  --rw [Nat.mul_left_cancel tg0 h]



 -- qify at h ⊢
  --polyrith
  --linear_combination h / 3



  --ring_nf
  --rw [mul_comm] at h
--  rw [mul_div_cancel_left h]
  --rw [Mathlib.Tactic.FieldSimp.fieldSimp] at h
  --simp? at h


/-

example (h : 2x + y = 14) (k : x = 3) : 6 + y = 14 :=
begin
  rw k,
  rw ←h,
  rw [mul_add, mul_comm],
  rw add_assoc,
  rw [add_comm 6 y, ←add_assoc, add_comm y 6],
end
-/

example (a b c x y z : ℕ) (h : ¬ x*y*z < 0) : c < a + 3*b := by
  qify
  qify at h
  /-
  h : ¬↑x * ↑y * ↑z < 0
  ⊢ ↑c < ↑a + 3 * ↑b
  -/
  sorry


/-
example (h : x + y = 10) (k : y = 5) : x = 5 := by
  rw [k] at h
  repeat rw [Nat.succ.injEq] at h
  exact h
  --simp only [Nat.succ.injEq] at h
  --simp? at h
  --exact h



example (x) : 0 + 0 + x + 0 + 0 = (x + (0 + 0)) := by
  simp only [Nat.add_zero, Nat.zero_add]
  --simp?
-/

example (h : 3*x - 2*y = 12) (k : y = 3) : x = 6 := by {
  have helper : 3 * x = 12 + 2 * y := by omega
  rw [k] at helper
  ring_nf at helper

  have helper2 : 18 = 6 * 3 := by ring
  rw [helper2] at helper
  exact Nat.mul_right_cancel three_pos helper

--  calc
--    x = 3 * x - 2 * y + 2 * y - 2 * x := by sorry
--    _ = 12 + 2*y - 2 * x := by rw [h]
--    _ = 12 - 2 * y - 3 * x + x := by ring_nf
}

example (x y : ℤ) (h1 : x = -3) (h2 : y = 10) : 2*x = -6 := by
  linear_combination (norm := skip) 2*h1
  simp

example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  linear_combination 1*h1 - 2*h2

example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  linear_combination h1 - 2*h2

example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  linear_combination (norm := ring_nf) -2*h2
  /- Goal: x * y + x * 2 - 1 = 0 -/

example (x y z : ℝ) (ha : x + 2*y - z = 4) (hb : 2*x + y + z = -2)
    (hc : x + 2*y + z = 2) :
    -3*x - 3*y - 4*z = 2 := by
  linear_combination ha - hb - 2*hc

example (x y : ℚ) (h1 : x + y = 3) (h2 : 3*x = 7) :
    x*x*y + y*x*y + 6*x = 3*x*y + 14 := by
  linear_combination x*y*h1 + 2*h2


axiom qc : ℚ
axiom hqc : qc = 2*qc

example (a b : ℚ) (h : ∀ p q : ℚ, p = q) : 3*a + qc = 3*b + 2*qc := by
  linear_combination 3 * h a b + hqc




example {x : ℝ} : (x/2)/2 = x/4 := by ring



-- logic
example {P Q : Prop} (h1 : P ∨ Q) (h2 : ¬ Q) : P := by

  --cases recursively, rcases
  rcases h1

  --obtain hP | hQ := h1
  --· apply hP
  --· contradiction


example (P Q : Prop) : P → (P ∨ ¬ Q) := by
  intro hP
  left
  apply hP



--linarith

-- Example 1

-- Example 2




example {x y : ℚ} (hx : x = 2) (hy : y ^ 2 = -7) : x + y ^ 2 = -5 :=
  calc
    x + y ^ 2 = x - 7 := by linarith [hy]
    _ = -5 := by linarith [hx]

example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 := by  linarith  

