import Game.Metadata
--import Lean

--open Lean
--#eval true LXOR true -- false
--#eval true LXOR false -- false
--#eval false LXOR true -- true
--#eval false LXOR false -- false

World "KnightsAndKnavesLemmas" 
Level 1

Title "" 

Introduction 
"
Before diving into an actual knights and knaves puzzle, lets explore basic results implied by the assumptions of this puzzle.

We will first look at the assumption that no one can be a knight and a knave at the same time.
It is represented as:
```
h : left ∩ right = ∅ 
```

In our problem, we have:
```
Aleft: A ∈ left
Aright: A ∈ right
```
This means that `A` belongs to both `left` and `right` i.e `A ∈ left ∩ right`. This would contradict `h` giving us `False` which is the goal.

To show `A ∈ left ∩ right`, use the following
```
Finset.mem_inter : a ∈ s₁ ∩ s₂ ↔ a ∈ s₁ ∧ a ∈ s₂
```
Use `have` so it would be added to the assumptions.
"

#check xor_iff_not_iff
#check Xor'
/- (a ∧ ¬ b) ∨ (b ∧ ¬ a) -/
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

implication for their statements with the negated version then why the two sets are disjoint
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
/-- dis22 -/
TheoremDoc disjoint as "disjoint" in "Knights and Knaves"
Statement disjoint (preamble := have A_not_in_Empty := Finset.not_mem_empty A) {inst : DecidableEq Inhabitant}(left : Finset Inhabitant ) (right : Finset Inhabitant)
(Aleft : A ∈ left)
(Aright : A ∈ right)
(h : left ∩ right = ∅)
: False := by
  #check Finset.mem_inter
  have := Finset.mem_inter.mpr ⟨Aleft, Aright⟩ 
  Hint "We know that `left ∩ right = ∅`, so replace it with `∅` using `rw` getting `A ∈ ∅`"
  rw [h] at this
  Hint "Remember that the empty is the set with no elements by definition. But we have found one, namely `A`. This directly contradicts the definition of `∅` so `contradiction` will work here."
  contradiction

#check Finset.inter_eq_right
-- Note that the forward direction is always true, and our assumption `h` wasn't used, but the backward direction is not always( We used `h` for that). This offers a simplification and decluttering of the proof state and will be followed from now on. The downside is an apparent loss of information, but the coming levels will show that this is not the case.

Conclusion 
"
This works for any two disjoint sets, specifically the two sets `Knight`,`Knave`.

Even if we didn't have `A_not_in_empty` in the assumptions, `contradiction` would have worked here because Lean knows the following theorem: 
```
Finset.not_mem_empty.{u_1} {α : Type u_1} (a : α) : a ∉ ∅
```
"

NewTheorem Finset.mem_inter disjoint
NewDefinition Finset inter
