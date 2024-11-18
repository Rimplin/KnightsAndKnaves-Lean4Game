import Game.Metadata

World "KnightsAndKnavesLemmas" 
Level 4

Title ""

Introduction 
"
The lemma `inright_notinleft` in this level applies to any two sets that are disjoint. The two we are interested in of course are `Knight`,`Knave`.

The reasoning goes as follows:

Assume `A ∈ left`. This is done using `intro` tactic.
"

Statement inright_notinleft
  {left : Finset K} {right : Finset K}
{inst : DecidableEq K}
(h : left ∩ right = ∅ )
(h' : A ∈ right) : A ∉ left := by
  intro a 
  Hint "Look familiar? This is exactly like the previous level which gave us `disjoint` theorem."
  exact disjoint h a h'

----
  --rw [Finset.inter_comm] at h
  --exact inleft_notinright h h' 

Conclusion 
"
"
