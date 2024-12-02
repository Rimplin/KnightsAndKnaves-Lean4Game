import Game.Metadata

Introduction 
"
`¬P` in Lean is defined as `P → False`. What this means is that we obtain `¬P` by assuming `P` and deriving a contradiction i.e constructing an object of type `False` i.e proving `False` which means that `False` is also true. 

`False` is the empty proposition, thus it has no introduction rule. It represents a contradiction.
What is a contradiction? Well, it is a propostional statement that is false for all possible values of its variables and deriving a contradiction means proving such a statement. By definition, `False` is always false. Another standard example of a contradiction is the following: 

$
\\begin{array}{|c|c|} 
\\hline
P & ¬P & P ∧ ¬P\\\\
\\hline
T & F & F \\\\
F & T & F \\\\
\\hline
\\end{array}
$

Another meaning for the term contradiction to refer to the assertion or proof of a propositional statement that is false for all possible values of its variables. We will use both interchangeably. So, deriving a contradiction means constructing such a proof.

"

/-
# what is false exactly

-- not a good explanation
## As a type
-- this is obviously not true???
--`False : Prop` is the type that has no inhabitants, i.e there is no object, say `h`, that is of type `False`. In other words, we cannot find an `h` such that `h :False`. This makes sense when considering that finding an `h:False` would mean we have proved something that is false. 
-/

example (hP : P)
  : P  := by

  {
   trivial
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
