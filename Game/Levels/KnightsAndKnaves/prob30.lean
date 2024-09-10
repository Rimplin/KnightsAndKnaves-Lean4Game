import Game.Metadata


example
{Knight : Set Inhabitant}
{Knave : Set Inhabitant}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{h2: B ∈ Knight ∨ B ∈ Knave }
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
    have negor := stAn.mp h_1 
    contradiction

  }





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/



-- NewTactic rw rfl
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

