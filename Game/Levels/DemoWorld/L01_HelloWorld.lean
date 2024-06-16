import Game.Metadata

World "DemoWorld"
Level 1
open Nat
Title "Hello World"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

--used in BasicAlgebra
Statement (h : x = 3) (g: y = 6) (i : z=10) : x + x = y := by
  Hint "You can either start using `{h}` or `{g}`."
  Branch
    rw [g]
    Hint "You should use `{h}` now."
    rw [h]
  rw [h]
  Hint "You should use `{g}` now."
  rw [g]

Conclusion "This last message appears if the level is solved."

/-
example (a b c d e f g : ℝ) (h : a + b + c = d - e + f - g) : a/2 + b/2 + c/2 = d/2 - e/2 + f/2 - g/2 :=
  field_simp
 --   rw ← add_assoc,
 --   rw h,
 --   ring,
 -- end
-/


example (y : ℕ) (h:3*y=12) : y=4 := by
  --hint
  omega
  --linarith

example (y : ℕ) (h:3*y=12) : y=4 := by
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


example (h:x=2) : x+2 =4 := by
{
norm_num
exact h
}
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
/-
example (h : 3x - 2y = 12) (k : y = 4) : x = 4 :=
begin
  rw k,
  rw ←h,
  
end
-/

/- Use these commands to add items to the game's inventory. -/


/-
:w:
- `simp`: This tactic simplifies expressions using a set of predefined rewrite rules. It's especially useful for basic simplifications involving arithmetic, inequalities, and logical connectives.

- `ring`: This tactic is more powerful and is specifically designed for proving equalities in commutative rings. It automatically applies a variety of algebraic properties such as associativity, commutativity, and distributivity to simplify expressions. It's particularly handy when dealing with expressions involving addition and multiplication.


-/

/--
Testing rw description1
-/
TacticDoc rw 

/--
Testing rfl description1
-/
TacticDoc rfl 
NewTactic rw rfl
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
