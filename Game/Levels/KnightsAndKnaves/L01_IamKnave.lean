import Game.Metadata


World "KnightsAndKnaves"
Level 1

Title ""

Introduction 
"
We have an inhabitant A which says the following statement: 
A : 'I am a knave.'

Merely uttering this statement is a contradiction. This is equivalent to the liars paradox. A saying 'I am a knave' is like A saying 'I am a liar' or 'I am lying'. If A were telling the truth, then A would be lying which is a contradiction. Similarly if A were lying then A would be telling the truth. Regardless of what A is, we fall into contradiction. The proof will take all cases for A, which are either the fact of always telling the truth(Knight) or always lying(Knave) and will show this contradiction(Knave) and will show this contradiction.
"

#check not_iff_self
Statement IamKnave
  --sets
  {Knight : Set Inhabitant} {Knave : Set Inhabitant}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{stA : A ∈ Knight  ↔ (A ∈ Knave) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave) }
  : False := by

  {
    rcases h1 with AKnight|AKnave

    · have := stA.mp AKnight
      exact disjoint h AKnight this
    
    · have := stA.mpr AKnave
      exact disjoint h this AKnave
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
