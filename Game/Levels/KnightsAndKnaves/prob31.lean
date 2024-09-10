import Game.Metadata

import Game.Metadata
--variable   (Knight : Set Inhabitant) (Knave : Set Inhabitant)

inductive Solution (Knight : Set Inhabitant) (Knave : Set Inhabitant)
| submit (h : A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) : Solution (Knight) (Knave)
-- i could obfuscate this by making a type that when given the correct argument solves the exercise.
example
  --sets
--  {Knight : Set Inhabitant} {Knave : Set Inhabitant}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{h2: B ∈ Knight ∨ B ∈ Knave }
{h3: C ∈ Knight ∨ C ∈ Knave }
{stA : A ∈ Knight  ↔ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave) }
{stB: B ∈ Knight ↔ (Knight = {A} ∨ Knight = {B} ∨ Knight = {C}) }
{stBn: B ∈ Knave ↔ ¬ (Knight = {A} ∨ Knight = {B} ∨ Knight = {C}) }
  : Solution Knight Knave:= by

  {
    have AKnave : A ∈ Knave := by 
      by_contra AKnight
      rw [NotKnave_KnightIff h h1] at AKnight
      have AKnave := stA.mp AKnight
      exact disjoint h AKnight AKnave.left 

    have BKnight : B ∈ Knight := by 
      by_contra BKnave
      rw [NotKnight_KnaveIff h h2] at BKnave
      push_neg at stBn 
      rw [not_and_or] at stAn
      rw [not_and_or] at stAn
      simp[AKnave] at stAn 
      simp[BKnave] at stAn 
      have := stBn.mp BKnave
      contrapose this
      rw [not_and_or]
      rw [not_and_or]
      right
      right
      push_neg
      have KSub : Knight ⊆ {A,B,C} := by sorry
      rw [Knave_NotKnightIff h h1] at AKnave
      rw [Set.subset_insert_iff_of_not_mem AKnave] at KSub
      rw [Knave_NotKnightIff h h2] at BKnave
      rw [Set.subset_insert_iff_of_not_mem BKnave] at KSub
      rw[ Set.subset_singleton_iff_eq] at KSub
      have nonemp : Knight ≠ ∅ := sorry
      cases KSub
      contradiction
      assumption
      -- have done this before, start from knight subset of A,B,C then remove... then state its non empty then do it...
    have CKnave : C ∈ Knave := by 
      by_contra CKnight
      #check Set.mem_singleton_iff
      #check Set.eq_singleton_iff_unique_mem
      have Ors := stB.mp BKnight
      cases Ors
      · rw [Set.eq_singleton_iff_unique_mem] at h_1 
        rw [Knave_NotKnightIff h h1] at AKnave
        exact AKnave h_1.left
      · cases h_1 
        · rw [NotKnave_KnightIff h h3] at CKnight
          rw [h_2] at CKnight
          rw [Set.mem_singleton_iff] at CKnight
          have : C ≠ B := sorry
          contradiction
        · rw [h_2] at BKnight
          rw [Set.mem_singleton_iff] at BKnight
          have : B ≠ C := sorry
          contradiction
    --constructor
    exact Solution.submit (And.intro AKnave ( (And.intro BKnight CKnave)))
    --constructor;assumption;constructor;assumption;assumption

    have AKiffKn : A ∈ Knight ↔ A ∈ Knave := by{ 
    constructor
    · sorry
    · sorry
     }
  }

example (S : Set K) (h : S ⊆ {A,B,C}) (h': A ∉ S) : S ⊆ {B,C} := by   
   
  #check Set.subset_insert_iff_of_not_mem




Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/



-- NewTactic rw rfl
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

