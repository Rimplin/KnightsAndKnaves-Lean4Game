import Game.Metadata
-- Knight_notKnave


World "KnightsAndKnavesLemmas"
Level 2

Title ""

Introduction 
"
"

-- two versions for proving the lemmas... i guess i can present the proof in the second version as its own level before knights and knaves approach 2
Statement Knight_NotKnave
  --sets
  {Knight : Set K} {Knave : Set K}
{h : Knight ∩ Knave = ∅ } --{h1 : Xor' (A ∈ Knight) (A ∈ Knave) } {h2: Xor' (B ∈ Knight)  (B ∈ Knave) }
(h' : A ∈ Knight)
  : A ∉ Knave := by

  {
   -- unfold Xor' at h1
   -- cases h1
   -- · exact h_1.right
   -- · exfalso
   --   exact h_1.right h'

    -- eliminate h1 , h2 and do by_contra
    by_contra
    have := Set.mem_inter h' a
    rw [h] at this
    contradiction
  }





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/



NewTactic by_contra
NewTheorem Set.mem_inter Knight_NotKnave
