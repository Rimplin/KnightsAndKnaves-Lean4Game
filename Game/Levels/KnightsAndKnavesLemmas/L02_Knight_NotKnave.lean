import Game.Metadata

World "KnightsAndKnavesLemmas"
Level 3

Title ""

Introduction 
"Note that this level is identical to the previous one except the fact that the set `left` is now called `Knight` and the set `right` is now called `Knave`. This level is to emphasize this pattern of reasoning that you will need to solve knights and knaves puzzles.

If you are a knight, then you are definitely not a knave. Recall that knights always tell the truth and knaves always lie.
"

Statement
  {A : Inhabitant}
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ } (h' : A ∈ Knight)
  : A ∉ Knave := by
  {
    exact inleft_notinright h h'
  }

Conclusion 
"
"

NewTactic by_contra
