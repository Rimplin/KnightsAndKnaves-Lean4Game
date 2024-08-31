import Game.Metadata
-- Knave_notKnight

World "KnightsAndKnavesLemmas"
Level 3

Title ""

Introduction 
"
"

Statement Knave_NotKnight
  --sets
  -- make them required arguments then make variables above it so user only puts h'
  {Knight : Set K} {Knave : Set K}
(h : Knight ∩ Knave = ∅ )
--(h1 : Xor' (A ∈ Knight) (A ∈ Knave) )
(h' : A ∈ Knave)
  : ¬ (A ∈ Knight) := by

  {
    -- h1
    --unfold Xor' at h1 
    --cases h1 
    --· exfalso
    --  exact h_1.right h'
    --· exact h_1.right
    by_contra
    have := Set.mem_inter a h'
    rw [h] at this
    contradiction
  }





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/


NewTheorem Knave_NotKnight
-- NewTactic rw rfl
