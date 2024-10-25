import Game.Metadata

World "KnightsAndKnavesLemmas"
Level 5

Title ""

Introduction 
"
Note that this is just like the previous level.
"

Statement 
  {inst : DecidableEq K}
  {Knight : Finset K} {Knave : Finset K}
(h : Knight ∩ Knave = ∅ )
(h' : A ∈ Knave)
  : ¬ (A ∈ Knight) := by

  {
    exact inright_notinleft h h'
  }

Conclusion 
"
"
