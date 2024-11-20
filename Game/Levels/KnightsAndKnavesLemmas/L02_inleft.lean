import Game.Metadata

World "KnightsAndKnavesLemmas" 
Level 2

Title "`inleft_notinright`" 

Introduction 
"
The lemma `inleft_notinright` in this level applies to any two sets that are disjoint. The two we are interested in of course are `Knight`,`Knave`.

The reasoning goes as follows:

Assume `A ∈ right`. This is done using `intro` tactic.
"

Statement inleft_notinright
  {left : Finset K} {right : Finset K}
{inst : DecidableEq K}
(h : left ∩ right = ∅ )
(h' : A ∈ left) : A ∉ right := by
  intro a 
  Hint "Look familiar? This is exactly like the previous level which gave us `disjoint` theorem."
  exact disjoint h h' a

Conclusion 
"
In the next level, you will use this theorem to prove that if `A` is a knight, then `A` is not a knave.
"
