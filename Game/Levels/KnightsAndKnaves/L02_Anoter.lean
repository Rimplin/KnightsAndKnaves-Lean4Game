import Game.Metadata

open Set

variable {K : Type}

World "KnightsAndKnaves"
Level 2

Title "lev 2"

Introduction "Hi"

Statement
  --sets
  (Knight : Set K ) (Knave : Set K)
  (h : Knight ∩ Knave = ∅ )
  (h1 : x ∈ Knight ∧ x ∉ Knave ∨ x ∈ Knave ∧ x ∉ Knight)
  (h2 : (y ∈ Knight ∧ y ∉ Knave) ∨ (y ∈ Knave ∧ y ∉ Knight) )
  -- theres x and y, x says at least one of us is a knave
  --rules of the game, i.e knights tell the truth but knaves lie
  (stx : x ∈ Knight → (x ∈ Knight ∧  y ∈ Knave)
                    ∨ (x ∈ Knave ∧ y ∈ Knight)
                    ∨ (x ∈ Knight ∧ y ∈ Knave)  )
  (stnx : x ∈ Knave → ¬ ( (x ∈ Knight ∧  y ∈ Knave)
                    ∨ (x ∈ Knave ∧ y ∈ Knight)
                    ∨ (x ∈ Knight ∧ y ∈ Knave) ) )
--goal
  : x ∈ Knight ∧ y ∈ Knave:= by
  {

   --rw [Xor'] at h1
   --rw [Xor'] at h2
   exact h1
   rw [Eq.rfl h1 ( (x ∈ Knight ∧ x ∉ Knave)  ∨ (x ∈ Knave ∧ x ∉ Knight ) )] at h1
   cases h1
   cases h2
  }





Conclusion "."

/- Use these commands to add items to the game's inventory. -/


-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
