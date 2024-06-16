import Game.Metadata
World "DemoWorld"
Level 1
open Nat
--open Group
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

example {r s : ℝ} (h1 : s = 3) (h2 : r + 2 * s = -1) : r = -7 :=
  calc
    r = r + 2 * s - 2 * s := by ring
    _ = -1 - 2 * s := by rw [h2]
    _ = -1 - 2 * 3 := by rw [h1]
    _ = -7 := by ring


example {a b m n : ℤ} (h1 : a * m + b * n = 1) (h2 : b ^ 2 = 2 * a ^ 2) :
    (2 * a * n + b * m) ^ 2 = 2 :=
  calc
    (2 * a * n + b * m) ^ 2
      = 2 * (a * m + b * n) ^ 2 + (m ^ 2 - 2 * n ^ 2) * (b ^ 2 - 2 * a ^ 2) := by ring
    _ = 2 * 1 ^ 2 + (m ^ 2 - 2 * n ^ 2) * (2 * a ^ 2 - 2 * a ^ 2) := by rw [h1,h2]
    _ = 2 := by ring

example {a b c d e f : ℤ} (h1 : a * d = b * c) (h2 : c * f = d * e) :
    d * (a * f - b * e) = 0 :=
  calc
    d * (a * f - b * e) 
    = a * d * f - d * b * e := by ring

    _ 
    = b * c * f - d * b * e := by rw [h1]  
    
    _ 
    = b * ( c * f) - d * b * e := by ring
    
    _
    = b * (d * e) - d * b * e := by rw [h2] 

    _
    = 0 := by ring

    
example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 := by
  {calc
    a = 2 * b + 5 := by rw [h1]
    _ = 2 * 3 + 5 := by rw [h2]
    _ = 11 := by ring
}


example {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=  
  calc
    x = x + 4 - 4 := by ring 
    _ = 2 -4 := by rw [h1]
    _ = -2 := by ring


example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 :=
  calc

    a 
    = (a - 5 * b ) + 5 * b := by ring 

    _  
    = 4 + 5 * b := by rw [h1]

    _ 
    = -6 + 5 * (b + 2) := by ring 

    _ 
    = -6 + 5 * 3 := by rw [h2]

    _
    = 9 := by norm_num

example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 :=
  calc
    w
    =( (3*w + 1) / 3) - 1/3 := by ring 

    _
    = 4/3 - 1/3 := by rw [h1]
     
    _ 
    = 1 := by norm_num

-- Example 1.3.5
example {x : ℤ} (h1 : 2 * x + 3 = x) : x = -3 :=

  calc
    x = 2 * x + 3 -x -3 := by ring
    _ = x - x -3 := by rw [h1] 
    _ = -3 := by ring 


example {x y : ℤ} (h1 : 2 * x - y = 4) (h2 : y - x + 1 = 2) : x = 5 :=
  calc
    x = (2 * x - y) + (y - x + 1 ) - 1 := by ring 
    _ = 4 + 2 - 1 := by rw [h1,h2] 
    _ = 5 := by ring

example {u v : ℚ} (h1 : u + 2 * v = 4) (h2 : u - 2 * v = 6) : u = 5 :=
  calc
    u = ((u+ 2*v) + (u - 2*v)) / 2 := by ring
    _ = (4+6)/2 := by rw [h1,h2] 
    _ = 5 := by ring

example {x y : ℝ} (h1 : x + y = 4) (h2 : 5 * x - 3 * y = 4) : x = 2 :=
  calc
    x = (3*(x+y) + (5 * x - 3 * y))/8 := by ring
    _ = (3*4 + 4 )/8 := by rw [h1,h2]
    _ = 2 := by ring


example {a b : ℚ} (h1 : a - 3 = 2 * b) : a ^ 2 - a + 3 = 4 * b ^ 2 + 10 * b + 9 :=
  sorry

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

/- Use these commands to add items to the game's inventory. -/


/-

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

