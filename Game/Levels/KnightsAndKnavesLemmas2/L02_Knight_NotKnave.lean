import Game.Metadata
-- Knight_notKnave


World "KnightsAndKnavesLemmas"
Level 2

Title ""

Introduction 
"
"

-- two versions for proving the lemmas... i guess i can present the proof in the second version as its own level before knights and knaves approach 2
Statement
  --sets
  {Knight : Set K} {Knave : Set K}
{h : Knight ∩ Knave = ∅ }
{h1 : Xor' (A ∈ Knight) (A ∈ Knave) }
{h2: Xor' (B ∈ Knight)  (B ∈ Knave) }
(h' : A ∈ Knight)
  : A ∉ Knave := by

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

