import Game.Metadata

World "KnightsAndKnavesLemmas" 
Level 6

Title "" 

Introduction 
"
Remember notright_left from logic world. You can go back if you wish before proceeding with this level: link to prev level.
"

Statement notinright_inleft
  {A : K}
  {left : Set K} {right : Set K}
  {LeftorRight : A ∈ left ∨ A ∈ right}
(h' : A ∉ right) : A ∈ left := by
  exact notright_left LeftorRight h'

Conclusion 
"
"

NewTheorem notright_left
