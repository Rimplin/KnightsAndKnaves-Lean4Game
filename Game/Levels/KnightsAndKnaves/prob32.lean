import Game.Metadata


example
  --sets
  {Knight : Set Inhabitant} {Knave : Set Inhabitant}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{h2: B ∈ Knight ∨ B ∈ Knave }
{h3: C ∈ Knight ∨ C ∈ Knave }
{stA : A ∈ Knight  ↔ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave) }
{stB: B ∈ Knight ↔ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knight ∨ A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knight ∨ A ∈ Knight ∧ B ∈ Knight ∧ C ∈ Knave) }
{stBn: B ∈ Knave ↔ ¬ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knight ∨ A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knight ∨ A ∈ Knight ∧ B ∈ Knight ∧ C ∈ Knave) }
  : A ∈ Knave ∧ C ∈ Knight := by

  {
 -- constructor
  have AKnave : A ∈ Knave := by
    by_contra AKnight
    rw [NotKnave_KnightIff h h1] at AKnight
    have knaves := stA.mp AKnight
    exact disjoint h AKnight knaves.left

  constructor
  exact AKnave
  rcases h2 with BKnight|BKnave
  ·  
    rw [not_or] at stBn
    rw [not_or] at stBn
    by_contra CKnave 
    have first : ¬(A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knight) := by 
      intro ands
      exact CKnave ands.right.right
    have second : ¬(A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knight) := by 
      intro ands 
      exact CKnave ands.right.right
    have third : ¬( A ∈ Knight ∧ B ∈ Knight ∧ C ∈ Knave) := by 
      intro ands
      rw [Knave_NotKnightIff h h1] at AKnave
      exact AKnave ands.left 
    have BKnave := stBn.mpr (And.intro first 
    (And.intro second third)) 
    exact disjoint h BKnight BKnave
  · have notallknaves := stAn.mp AKnave
    rw [not_and_or] at notallknaves 
    have : ¬(A ∉ Knave) := by exact not_not.mpr AKnave
    have BC := notleft_right notallknaves this 

    rw [not_and_or] at BC 
    have : ¬(B ∉ Knave) := by exact not_not.mpr BKnave
    have CKnight := notleft_right BC this
    rw [Knight_NotKnaveIff h h3] 
    assumption


  }





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/



-- NewTactic rw rfl
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

