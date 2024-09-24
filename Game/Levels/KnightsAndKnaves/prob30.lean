import Game.Metadata


example
{Knight : Set Inhabitant}
{Knave : Set Inhabitant}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{stA : A ∈ Knight  ↔ (A ∈ Knave ∨ (2+2=5) ) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∨ (2+2=5) ) }
  :False  := by

  {
  -- you could go to a meta level and say the author of the problem is not a knight
  cases h1
  · have cont := stA.mp h_1
    cases cont
    · exact disjoint h h_1 h_2
    · contradiction
  · have : A ∈ Knave ∨ 2 + 2=5 := by left ; assumption
    have nor := stAn.mp h_1 
    contradiction

  }


-- if else version
example
{Knight : Set Inhabitant}
{Knave : Set Inhabitant}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{stA : A ∈ Knight  ↔ (A ∈ Knave ∨ (2+2=5) ) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∨ (2+2=5) ) }
  :False  := by
  if AKnight : A ∈ Knight then
    have cont := stA.mp AKnight
    if AKnave : A ∈ Knave then 
      rw [Knave_NotKnightIff h h1] at AKnave
      contradiction
    else 
      have := notleft_right cont AKnave
      contradiction
    --cases cont
    -- exact disjoint h h_1 h_2
    -- contradiction

    
  else 
    rw [NotKnight_KnaveIff h h1] at AKnight
    have := stAn.mp AKnight
    exact this (by left ; assumption)
  


Conclusion 
"
"

