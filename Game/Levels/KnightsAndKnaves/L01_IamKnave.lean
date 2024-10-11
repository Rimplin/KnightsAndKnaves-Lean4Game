import Game.Metadata


World "KnightsAndKnaves"
Level 1

Title ""

Introduction 
"
Let's solve the previously mentioned 'I am a knave' puzzle.

Suppose we have an inhabitant A which says: 
A : 'I am a knave.'

Merely uttering this statement is a contradiction. This is equivalent to the liars paradox(https://en.wikipedia.org/wiki/Liar_paradox). A saying 'I am a knave' is like A saying 'I am a liar' or 'I am lying'. 

If A were telling the truth(i.e a knight), then A would be lying which is a contradiction. 

Similarly if A were lying(i.e a knave) then A would be telling the truth. 

Regardless of what A is, we fall into contradiction. The proof will take all cases for A, which are either the fact of always telling the truth(Knight) or always lying(Knave) and will show this contradiction(Knave) and will show this contradiction.

Remember that is either a knight or a knave, represented by `h1` , and our reasoning was taking every case and showing that we reach the same conclusion in both. This is a proof by cases.

For this, we need the `cases` tactic. Try `cases h1` and see what happens

"

#check not_iff_self
Statement IamKnave
  --sets
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{stA : A ∈ Knight  ↔ (A ∈ Knave) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave) }
  : False := by

  {
  cases h1
  Hint 
  "Notice that `h1` is now replaced by `h_1`, and we have two goals to prove instead of one. The difference between each is that in the first, A is a knight and in the second A is a knave.  
  
  Use the fact that A is a knight to conclude...
  "

  have := stA.mp h_1
  Hint "So now we have that A is a knight, A is a knave. But this contradicts the fact that these two sets are disjoint."
  exact disjoint h h_1 this

  Hint "Notice that h_1 is now `A ∈ Knave`. There are multiple ways to get a contradiction here. Either by concluding `A ∉ Knave` from `stAn` or by concluding `A ∈ Knight` from `stA` which would be identical."
  have := stA.mpr h_1
  exact disjoint h this h_1

   -- rcases h1 with AKnight|AKnave

   -- · have := stA.mp AKnight
   --   exact disjoint h AKnight this
   -- 
   -- · have := stA.mpr AKnave
   --   exact disjoint h this AKnave
  }


#check not_iff_self
example
  {Knight : Set Inhabitant} {Knave : Set Inhabitant}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{stA : A ∈ Knight  ↔ (A ∈ Knave) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave) }
  : False := by

  {
    have := Iff.symm stAn
    apply not_iff_self 
    exact this
  }



Conclusion 
"
"
