--prove 
--theorem and_imp {a : Prop} {b : Prop} {c : Prop} :
--a ∧ b → c ↔ a → b → c
--
/-
In this level, you will combine what you learned about conjunctions and implications to prove the goal.
-/

#check iff_def

variable {emTruth : (P : Prop) → P = True ∨ P = False}
-- the statement that a always has the same truth value as b is true, meaning that a is logically equivalent to b.
example : (((¬P ∨ Q) ↔ (P → Q)) = True) := by 
  cases emTruth P
  · cases emTruth Q
    · 
      -- could make template and write hints here
      rw [h,h_1]
      rw [true_implies]
      rw [or_true]
      rw [true_iff]

    · sorry
  · cases emTruth Q
    · sorry
    · sorry

-- template 
/-

  cases emTruth P
  · cases emTruth Q
    · sorry
    · sorry
  · cases emTruth Q
    · sorry
    · sorry
    -/
