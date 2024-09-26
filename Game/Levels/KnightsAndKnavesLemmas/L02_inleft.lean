import Game.Metadata


World "KnightsAndKnavesLemmas" 
Level 2

Title "" 

Introduction 
"
We will use this to prove several helpful lemmas in the context of the knights and knaves puzzle. Note that these lemmas apply to any two sets.
"
#check inleft_notinright
Statement inleft_notinright
  --sets
  {left : Set K} {right : Set K}
(h : left ∩ right = ∅ )
(h' : A ∈ left) : A ∉ right := by
  intro a 
  have := Set.mem_inter h' a
  rw [h] at this
  #check Set.mem_empty_iff_false
  #check Set.not_mem_empty -- let preamble execute this in a have so in appears in the assumptions...
  contradiction





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

--NewTactic 
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

