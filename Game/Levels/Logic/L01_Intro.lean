import Game.Metadata


World "Logic"
Level 1

Title "Intro"

Introduction
" 
This should look familiar.

If it doesn't, then replace `P` by `x=2`.

`hP` is of type `P` and `P` is of type `Prop`. So, `hP` is a proof of `P`. Our goal is to prove `P`. We already have such a proof which is `hP`, `hP` is EXACTLY what we need to prove the goal. The type of `hP` EXACTLY matches the goal.
"

--This is to emphasize that for the tactic `exact h`, the type of h doesn't matter.
--<img src=\"data/g/JadAbouHawili/testing-leangame/Truth-Table-And.png\"/>
--
--$\\displaystyle {\\frac {P\\lor Q,\\neg P}{\\therefore Q}}$
--
--$\\iff$
--
-- $ \\begin{tabular}{ c c c }cell1 & cell2 & cell3 \\ cell4 & cell5 & cell6 \\  cell7 & cell8 & cell9    \\end{tabular}$

--``
--<img src=\"https://url.com/to/image\"/>
--```
--
--Local images can currently only be included with a hack:
--
--Images in the game's `images/` folder will be accessible at `data/g/[user]/[repo]/[image].[png|jpg|…]`
--<img src='data/g/hhu-adam/testing-leangame/images/Truth-Table-And.png' />

--<img src='images/Logic/Truth-Table-And.png' />

Statement (P Q R : Prop) (hP: P) (hQ: Q) (hR : R)
  : P := by
  {
   Hint (hidden := true) "Type `exact hP`!"
   exact hP
  }

--#check (@(iff_eq_eq.mpr)) P P
#check iff_eq_eq.mp

example : P = (P ∧ P) := by 
  --apply @iff_eq_eq.mpr P P 
  apply iff_eq_eq.mp 
  constructor 
  intro hp ; constructor; repeat assumption
  intro pp ; exact pp.left

example  (h1 : P ∨ Q) (h2 : ¬ Q) : P := by
  obtain hP | hQ := h1
  · apply hP
  · contradiction


example (P Q : Prop) : P → (P ∨ ¬ Q) := by
  intro hP
  left
  apply hP

example  : (P ∨ P) ↔ P := by
  constructor
  · intro h
    obtain h1 | h2 := h
    · apply h1
    · apply h2
  · intro h
    left
    apply h

example : (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) := by
  constructor
  · intro h
    obtain ⟨h1, h2 | h2⟩ := h
    · left
      constructor
      · apply h1
      · apply h2
    · right
      constructor
      · apply h1
      · apply h2

  · intro h
    obtain ⟨h1 , h2⟩ := h
    constructor
    apply h1
    left
    apply h2

    constructor
    apply h.left
    right
    apply h.right

example (h : P ∧ Q) : P ∨ Q := by
  left
  exact h.left


example {P Q R : Prop} (h1 : P → Q) (h2 : P → R) (h3 : P) : Q ∧ R := by
  exact And.intro (h1 h3) (h2 h3)



example : ¬(P ∧ ¬ P) := by
  intro h
  have h1 := h.left
  have h2 := h.right
  exact h2 h1

example (h1 : P ↔ ¬ Q) (h2 : Q) : ¬ P := by
  obtain ⟨p,nq⟩ := h1
  intro h
  exact (p h) h2

example (h1 : P ∨ Q) (h2 : Q → P) : P := by
  cases h1
  exact h
  exact h2 h

example (h : P ↔ Q) : (P ∧ R) ↔ (Q ∧ R) := by
obtain ⟨pq,qp⟩ := h
constructor

--pick_goal
intro h
exact And.intro (pq h.left) h.right
--swap
intro h
exact And.intro (qp h.left) h.right

example : (P ∧ P) ↔ P := by
  constructor

  intro h
  exact h.left

  intro h
  exact And.intro h h

example : (P ∨ Q) ↔ (Q ∨ P) := by
  constructor

  intro h
  cases h
  right
  exact h_1
  left
  exact h_1

  intro h
  cases h
  right
  exact h_1
  left
  exact h_1


example : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor

  intro h
  constructor

  intro h1
  exact h (Or.inl h1)

  intro h1
  exact h (Or.inr h1)

  intro h
  intro h1
  cases h1
  exact h.left h_1
  exact h.right h_1
--library_search

example : ¬ (¬ P) ↔ P := by
  constructor
  · intro h
    push_neg at h
    exact h

  · intro h
    push_neg 
    exact h

Conclusion 
"
In the next levels, we will discuss how to construct new propositions from old ones whose meaning and truth value would depend on those old ones. 
"

/-
## Overview
Having h : P and P as your goal, exact h will close the goal. exact h asserts that h is exactly whats needed to prove the goal which makes sense because h is a proof of P.(It doesn't matter what P is)
-/
NewTactic intro

NewDefinition «Prop»
