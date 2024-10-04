import Game.Metadata
-- Knight_notKnave


World "KnightsAndKnavesLemmas"
Level 3

Title ""

Introduction 
"Note that this level is identical to the previous one except the fact that the set `left` is now called `Knight` and the set `right` is now called `Knave`. This level is to emphasize this pattern of reasoning that you will need to solve knights and knaves puzzles.

If you are a knight, then you are definitely not a knave. Recall that knights always tell the truth and knaves always lie.
"

-- two versions for proving the lemmas... i guess i can present the proof in the second version as its own level before knights and knaves approach 2

--TheoremDoc notKnave_Knight as "notKnave_Knight" in "Logic"
/-- test -/
---- notKnave_Knight (h : ¬ (x ∈ Knave) ) : x ∈ Knight
--TheoremDoc notKnave_Knight as "notKnave_Knight" in "Logic"
--Statement notKnave_Knight 

--TheoremDoc Knight_NotKnave as "Knight_NotKnave" in "Knights and Knaves"
Statement  
  --sets
  {A : Inhabitant}
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ } (h' : A ∈ Knight)
  : A ∉ Knave := by

  {
    -- eliminate h1 , h2 and do by_contra
    --intro a
    --have := Set.mem_inter h' a
    --rw [h] at this
    --contradiction
    exact inleft_notinright h h'
  }





Conclusion 
"
"

NewTactic by_contra
