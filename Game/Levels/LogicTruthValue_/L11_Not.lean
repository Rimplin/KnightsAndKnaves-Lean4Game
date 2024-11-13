import Game.Metadata

World "LogicTruthValue_" 
Level 6

Title "Not Connective, ¬" 

#check not_false
/-

Index
https://leanprover-community.github.io/mathlib4_docs/

Init.Core
https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#not_true

Init.Core
https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#Iff

Init.Core
https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext

Mathlib.Logic.Basic
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Basic.html#of_not_not

lean4/src/Init/Core.lean at daa22187642d4cf6954c39a23eab20d8a8675416 · leanprover/lean4 · GitHub
https://github.com/leanprover/lean4/blob/daa22187642d4cf6954c39a23eab20d8a8675416/src/Init/Core.lean#L1391-L1391

Init.Core
https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#Iff.of_eq

lean4/src/Init/Core.lean at daa22187642d4cf6954c39a23eab20d8a8675416 · leanprover/lean4 · GitHub
https://github.com/leanprover/lean4/blob/daa22187642d4cf6954c39a23eab20d8a8675416/src/Init/Core.lean#L803-L803

Mathlib.Logic.Basic
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Basic.html#iff_eq_eq

Init.Core
https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#iff_of_eq

Init.Core
https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#iff_iff_eq

lean4/src/Init/Core.lean at daa22187642d4cf6954c39a23eab20d8a8675416 · leanprover/lean4 · GitHub
https://github.com/leanprover/lean4/blob/daa22187642d4cf6954c39a23eab20d8a8675416/src/Init/Core.lean#L1390-L1390

Init.Core
https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext

lean4/src/Init/Core.lean at daa22187642d4cf6954c39a23eab20d8a8675416 · leanprover/lean4 · GitHub
https://github.com/leanprover/lean4/blob/daa22187642d4cf6954c39a23eab20d8a8675416/src/Init/Core.lean#L1304-L1304

Init.Ext
https://leanprover-community.github.io/mathlib4_docs/Init/Ext.html#propext_iff

biconditional at DuckDuckGo
https://start.duckduckgo.com/lite/?q=biconditional

Logical biconditional - Wikipedia
https://en.wikipedia.org/wiki/Logical_biconditional#Colloquial_usage
-/

/-
Another way to say that `P = False` is by saying `¬P = True`. These two statements say the same thing. This is how we will define `¬`.


`¬` is defined to satisfy the following properties:
`(P = True) → (¬P = False)`
`(P = False) → (¬P = True)`
If `P` is True, then `¬P` is False.
If `P` is False, then `¬P` is True.

If `¬P` is False, then `P` is True.
If `¬P` is False, then `P` is True.

Two nots give a true. Double negatives. Two negatives make/resolve into a positive.
Intuitvely, this fits how negation or 'not' works in language.

# What is `False` exactly? 

## How to prove `False` and what are the consequences? -- this has been introduced in the previous level...
This is what you did in the previous level. This section is just reiterating that point. 

It should be clear that to get to false, you would need to prove `¬P`, and `P`. Then given such a proof state:
```
hnP : ¬P
hP : P
```
we can obtain false by `hnP hP`.
Proving a proposition and its negation is a special case of 'deriving a contradiction' because we have proven `p ∧ ¬p` which is always false. A logical system that has this quality is called an inconsistent system.

# Defining `¬`

## But what is `False` exactly?(now we know what `False` is from the truth value perspective so this would need a rewrite in logic world, no it doesn't because we were dealing with `= False` but now we are dealing with `→ False`).
For now, just know that `False` is a type that has no introduction rule and that proving `False` means deriving a contradiction. So, to prove `¬p` , you must assume `p` and derive a contradiction. We will explain in more detail what is meant by 'contradiction'.
-/

Introduction 
"
In this level we introduce the negation, the `¬` connective (read as 'not').

Notice that this is the first logical connective that applies on one proposition only and not two.

The job of this connective(as the name implies), is to negate a proposition meaning that:
- For `P` true, `¬P` is false.
- For `P` false, `¬P` is true.

In truth table form:
$
\\begin{array}{|c|c|} 
\\hline
P & ¬P \\\\
\\hline
T & F \\\\
F & T \\\\
\\hline
\\end{array}
$

But we don't need to introduce a new symbol, it can be defined in terms of what we already know.

Consider the following truth table: 
$
\\begin{array}{|c|c|} 
\\hline
P & P → False \\\\
\\hline
T & F  \\\\
F & T  \\\\
\\hline
\\end{array}
$

Notice that regardless of the truth value of `P`, the two propositions `¬P` and `P → False` have the same truth table. Therefore, they can be used interchangeably.(we say that these two expressions are logically equivalent, but let's leave this to a future level)

In fact, this is how `¬P` is defined in Lean.

`¬P` being true tells us that a proof of `P` gives us a proof of `False`. We have a proof of `P`. Therefore we can obtain a proof of `False` which is the goal.
"

/-
It should be clear that to get to false, you would need to prove `¬P`, and `P`. Then given such a proof state:
```
hnP : ¬P
hP : P
```
we can obtain false by `hnP hP`.


Note that `¬P` is also a proposition, so `¬ (¬P)` is a valid expression. Moreover, `¬ (¬P)` is a proposition so `¬ (¬ (¬P))` or `¬¬¬P` is a valid expression (and so on).

The empty type. It has no constructors.
`False` is the empty proposition, thus it has no introduction rule. It represents a contradiction. Finding a 
What is a contradiction? Well, it is a propostional statement that is false for all possible values of its variables. Constructing a term(i.e a proof) of this type is proving something that is false. The standard example of a contradiction is the following: 

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

# What is `False` exactly? 

## How to prove `False` and what are the consequences? -- this has been introduced in the previous level...
This is what you did in the previous level. This section is just reiterating that point. 

Proving a proposition and its negation is a special case of 'deriving a contradiction' because we have proven `p ∧ ¬p` which is always false. A logical system that has this quality is called an inconsistent system.

## Principle of explosion
Moreover, `False` has no introduction rule , so the reasoning described above is the only way to obtain an object of type `False`. If you were able to find `h:False` i.e prove `False` then our system is worthless because we can prove anything. To reiterate, such a system would be called an inconsistent system because of a contradiction.
-/

#check not_of_eq_false
#check eq_false
Statement {P: Prop}
{hP : P} {hnP : ¬P}
: False := by{
  exact hnP hP 
 } 
example (hPnp : P ∧ ¬P )
  : False  := by
  {
   exact hPnp.right hPnp.left
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

Conclusion 
"
In the next level, we will explore what it means to have proven `False`.
"
