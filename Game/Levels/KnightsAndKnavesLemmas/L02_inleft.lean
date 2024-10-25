import Game.Metadata


World "KnightsAndKnavesLemmas" 
Level 2

Title "" 

Introduction 
"
We will use this to prove several helpful lemmas in the context of the knights and knaves puzzle. Note that these lemmas apply to any two sets.

The reasoning goes as follows:
Assume `A ∈ right`.
Then `A ∈ left ∩ right` 
But `left ∩ right = ∅ `, so `A ∈ ∅`. 
This is a contradiction
"
#check inleft_notinright
Statement inleft_notinright
  --sets
  {left : Set K} {right : Set K}
(h : left ∩ right = ∅ )
(h' : A ∈ left) : A ∉ right := by
  Hint "Assume `A ∈ right` using `intro`"
  intro a 
  Hint 
  "
  We know that `A ∈ left`, `A ∈ right`. So `A ∈ left ∩ right`.
  "
  have := Set.mem_inter h' a
  Hint " But left ∩ right is empty. So , A ∈ ∅ "
  rw [h] at this
  Hint "this is a contradiction of course"
  #check Set.mem_empty_iff_false
  #check Set.not_mem_empty 
  -- let preamble execute this in a have so in appears in the assumptions...
  contradiction

Conclusion 
"
"
