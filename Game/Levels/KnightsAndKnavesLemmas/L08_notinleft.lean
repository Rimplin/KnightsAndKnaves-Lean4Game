import Game.Metadata
World "KnightsAndKnavesLemmas" 
Level 8

Title "`notinleft_inright`"

Introduction 
"
"

Statement notinleft_inright
  {A : K}
  {left : Finset K} {right : Finset K}
  (LeftorRight : A ∈ left ∨ A ∈ right)
(h' : A ∉ left) : A ∈ right := by
  exact notleft_right LeftorRight h'

Conclusion 
"
"

NewTheorem notleft_right
