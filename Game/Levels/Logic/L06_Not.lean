import Game.Metadata


World "Logic" 
Level 6

Title "Not, ¬" 

Introduction 
"
```
| P |  ¬P    |
|---|--------|
| T |   F    |
| F |   T    |
```
The ¬ symbol flips the truth value of `P`.
As you can see in the above truth table, if `P` were true then `¬P` would be false and vice versa
`¬P` in Lean is defined as `P → False`. What this means is that we obtain `¬P` by assuming `P` and deriving a contradiction i.e constructing an object of type `False` which is impossible.

"

Statement (hP : P)
  : P  := by

  {
   exact hP
   --trivial
  }

variable (R : Type*) [Ring R]
#check (add_assoc : ∀a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀a b : R, a + b = b + a)
#check (zero_add : ∀a : R, 0 + a = a)
#check (add_left_neg : ∀a : R, -a + a = 0)
#check (mul_assoc : ∀a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀a : R, a * 1 = a)
#check (one_mul : ∀a : R, 1 * a = a)
#check (mul_add : ∀a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀a b c : R, (a + b) * c = a * c + b * c)

variable (R : Type*) [CommRing R]
variable (a b c d : R)
example : c * b * a = b * (a * c) := by ring
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring
example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring
example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
rw [hyp, hyp']
ring

namespace MyRing
variable {R : Type*} [Ring R]
theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]
theorem add_right_neg (a : R) : a + -a = 0 := by rw [add_comm, add_left_neg]
#check MyRing.add_zero
#check add_zero
end MyRing


theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [←mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

Conclusion ""

/- Use these commands to add items to the game's inventory. -/

-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
