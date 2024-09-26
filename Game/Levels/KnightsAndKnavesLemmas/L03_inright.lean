import Game.Metadata


World "KnightsAndKnavesLemmas" 
Level 4

Title "" 

Introduction 
"
"

Statement inright_notinleft
  --sets
  {left : Set K} {right : Set K}
(h : left ∩ right = ∅ )
(h' : A ∈ right) : A ∉ left := by
  intro a 
  have := Set.mem_inter h' a
  rw [Set.inter_comm] at h
  rw [h] at this
  contradiction





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

--NewTactic 
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

