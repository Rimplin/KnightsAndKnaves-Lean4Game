import Game.Metadata


example
{inst : DecidableEq Inhabitant}
{Knight : Finset Inhabitant}
{Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{stA : A ∈ Knight  ↔ (A ∈ Knave ∨ (2+2=5) ) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∨ (2+2=5) ) }
  :False  := by

  {
  simp at stA
  simp at stAn
  #check IamKnave
  exact IamKnave h h1 stA


  -- you could go to a meta level and say the author of the problem is not a knight
  -- use simp to simplify stA
  --cases h1
  --· have cont := stA.mp h_1
  --  cases cont
  --  · exact disjoint h h_1 h_2
  --  · contradiction
  --· have : A ∈ Knave ∨ 2 + 2=5 := by left ; assumption
  --  have nor := stAn.mp h_1 
  --  contradiction

  }


-- if else version
example
{inst : DecidableEq Inhabitant}
{Knight : Finset Inhabitant}
{Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{stA : A ∈ Knight  ↔ (A ∈ Knave ∨ (2+2=5) ) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∨ (2+2=5) ) }
  :False  := by
  if AKnight : A ∈ Knight then
    have cont := stA.mp AKnight
    if AKnave : A ∈ Knave then 
      rw [inright_notinleftIff h1 h] at AKnave
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
