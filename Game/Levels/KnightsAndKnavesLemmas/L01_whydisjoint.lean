import Game.Metadata
--import Lean

--open Lean
--#eval true LXOR true -- false
--#eval true LXOR false -- false
--#eval false LXOR true -- true
--#eval false LXOR false -- false

World "KnightsAndKnavesLemmas" 
Level 1

Title "`disjoint` theorem"

Introduction 
"
Before diving into an actual knights and knaves puzzle, lets explore basic results implied by the assumptions of this puzzle.

We will first look at the assumption that no one can be a knight and a knave at the same time.
It is represented as:
```
h : Knight ∩ Knave = ∅ 
```

The reasoning in this level applies to any two finite sets, so we use the two sets `left`,`right`.

In our problem, we have:
```
Aleft: A ∈ left
Aright: A ∈ right
h : left ∩ right = ∅
```
This means that `A` belongs to both `left` and `right` i.e `A ∈ left ∩ right`.

Prove `A ∈ left ∩ right` using `AinBothInter : A ∈ left ∧ A ∈ right → A ∈ left ∩ right`.
"

/-
So, we do have someone who is both a knight and a knave. This contradicts `h`.

This would contradict `h` giving us `False` which is the goal.

To show `A ∈ left ∩ right`, use the following
```
Finset.mem_inter : a ∈ s₁ ∩ s₂ ↔ a ∈ s₁ ∧ a ∈ s₂
```
Use `have` so it would be added to the assumptions.

Heres an example:
`have twoEqualstwo : 2=2 := rfl` will add an object named `twoEqualstwo` of type `2=2` to the proof state which would look as follows:
```
Assumptions:
twoEqualstwo : 2=2
```

You can choose any name after `have` and any type after `:`.
-/
/-
Heres an example,
Given the following proof state:
```
Assumptions:
four_pos : 0 < 4
h : 4 * y = 16
```
`have yEqFour := Nat.mul_left_cancel four_pos h` will result in the following proof state:
```
Assumptions:
four_pos : 0 < 4
h : 4 * y = 16
yEqFour : y = 4
```
-/

#check xor_iff_not_iff
#check not_iff
/-
A ∈ Knight ∧ A ∉ Knave ∨ A ∈ Knave ∧ A ∉ Knight
-/

/-
journey of formalization:
The two sets Knight and Knave must be disjoint. You can't telll the truth and lie at the same time because if that is true, then you would be asserting `p ∧ ¬p` which can be used to derive `False` i.e a contradiction( you have shown in a previous level that `p ∧ ¬p → False`. This is not something we want, the puzzles would be meaningless.
-/ 

-- steps for showcasing formalization
/-
the objects in question like A,B,C

implication for their statements with the negated version
-/

-- prefered
/-
 extend contradiction to detect this?
extending contradiction still seems to require passing the arguments, rendering it pointless.

--syntax:10 (name := lxor) term:10 term:11 " LXOR " term:12 : term
--
--@[macro lxor] def lxorImpl : Macro
--  | `($l:term $k:term LXOR $r:term) => `(disjoint $k $l $r) -- we can use the quotation mechanism to create `Syntax` in macros
--  | _ => Macro.throwUnsupported
--
--macro_rules
--  | `(contradictiondis $l:term $r:term) => `(disjoint $l $r)
-/

-- consider using this, if there is a finset version
#check Set.mem_empty_iff_false
#check Set.not_mem_empty 

Statement disjoint (preamble := have A_not_in_Empty := Finset.not_mem_empty A) {inst : DecidableEq Inhabitant}{left : Finset Inhabitant } {right : Finset Inhabitant}
(Aleft : A ∈ left)
(Aright : A ∈ right)
(h : left ∩ right = ∅)
(AinBothInter : A ∈ left ∧ A ∈ right → A ∈ left ∩ right)
(AnotEmpty : A ∉ (∅ : Finset Inhabitant) )
: False := by
  #check Finset.mem_inter
  Template
  have  AinInter : A ∈ left ∩ right:=by Hole exact AinBothInter ⟨Aleft, Aright⟩ 
  Hint "
But,  `left ∩ right = ∅` so `A ∈ ∅` 

  We know that `left ∩ right = ∅`, so replace it with `∅` using `rw` getting `A ∈ ∅`"
  Hole
  rw [h] at AinInter
  Hint "
So now we have `A ∈ ∅` but the empty set is by defintion the set with no elements i.e `¬ (A ∈ ∅)` written as `A ∉ ∅`. Therefore, `False`.
"
  Hint (hidden := true) " Remember `A ∉ ∅` is `A ∈ ∅ → False` , or use `contradiction`"
  contradiction

#check Finset.inter_eq_right
--    But we have found one, namely `A`. This directly contradicts the definition of `∅` so `contradiction` will work here."

-- Note that the forward direction is always true, and our assumption `h` wasn't used, but the backward direction is not always( We used `h` for that). This offers a simplification and decluttering of the proof state and will be followed from now on. The downside is an apparent loss of information, but the coming levels will show that this is not the case.

Conclusion
"
We have proved the following theorem which you can use in future levels:
```
theorem disjoint
(h : left ∩ right = ∅ )
(Aleft : A ∈ left)
(Aright : A ∈ right)
: False
```

Example:
For a goal `False`:
```
exact disjoint h Aleft Aright
```
would close the goal

The two assumptions `AinInter` and `AnotEmpty` are always true for any sets, and are available in Lean but where added explictly to this level for your convenience. So, the `disjoint` theorem can just use them instead of having to take them as arguments.

The theorem `disjoint` can be used for any two disjoint sets, specifically the two sets `Knight`,`Knave`.
"
/-
Even if we didn't have `A_not_in_empty` in the assumptions, `contradiction` would have worked here because Lean knows the following theorem: 
```
Finset.not_mem_empty.{u_1} {α : Type u_1} (a : α) : a ∉ ∅
```
-/

NewTheorem Finset.mem_inter disjoint
NewDefinition Finset inter KnightsKnaves mem
NewTactic «have» 
