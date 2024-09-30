import Game.Metadata




example
  --sets
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{stA : A ∈ Knight  ↔ (A ∈ Knave ∨ B ∈ Knight) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∨ B ∈ Knight) }
  : A ∈ Knight ∧ B ∈ Knight := by

  {
  -- fully optimized book solution

    have AnKnave : A ∉ Knave := by 
      intro AKnave
      have Or : A ∈ Knave ∨ B ∈ Knight := by 
      {
        left
        assumption
      }

      have := stAn.mp AKnave 
      contradiction

    have AKnight := notinright_inleft h1 AnKnave
    have BKnight := stA.mp AKnight
    constructor
    assumption 
    exact notleft_right BKnight AnKnave


  ----
    --#check imp_or 
    --#check imp_not_self

    --have forward := stA.mp
    --rw [imp_or] at forward 
    --rw [inright_notinleftIff h1 h] at forward  
    --rw [imp_not_self] at forward
    --cases h1 
    --· have := not_not.mpr h_1 
    --  have AKBK := notleft_right forward this
    --  constructor
    --  assumption
    --  exact AKBK h_1
    --· 
    --  have cont : A ∈ Knave ∨ B ∈ Knight := by left; assumption 
    --  have nimp := stAn.mp h_1
    --  contradiction
  }





Conclusion 
"
"




-- NewTactic rw rfl
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
 
