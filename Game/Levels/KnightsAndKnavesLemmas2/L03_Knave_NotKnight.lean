import Game.Metadata
-- Knave_notKnight


World "KnightsAndKnavesLemmas"
Level 3

Title ""

Introduction 
"
"

Statement
  --sets
  {Knight : Set K} {Knave : Set K}
{h : Knight ∩ Knave = ∅ }
{h1 : Xor' (A ∈ Knight) (A ∈ Knave) }
(h' : A ∈ Knave)
  : ¬ (A ∈ Knight) := by

  {

    unfold Xor' at h1
    have h' := eq_true h'
    rw [h'] at h1
    simp at h1 
    assumption
  }





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/



-- NewTactic rw rfl
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

