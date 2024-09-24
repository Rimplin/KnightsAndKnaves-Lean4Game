import Game.Metadata




example
  --sets
  {Knight : Set Inhabitant} {Knave : Set Inhabitant}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{stA : A ∈ Knight  ↔ (A ∈ Knave ∨ B ∈ Knight) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∨ B ∈ Knight) }
  : A ∈ Knight ∧ B ∈ Knight := by

  {
    #check imp_or 
    #check imp_not_self
    have forward := stA.mp
    rw [imp_or] at forward 
    rw [Knave_NotKnightIff h h1] at forward  
    rw [imp_not_self] at forward
    cases h1 
    · have := not_not.mpr h_1 
      have AKBK := notleft_right forward this
      constructor
      assumption
      exact AKBK h_1
    · 
      have cont : A ∈ Knave ∨ B ∈ Knight := by left; assumption 
      have nimp := stAn.mp h_1
      contradiction
  }





Conclusion 
"
"




-- NewTactic rw rfl
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
 
