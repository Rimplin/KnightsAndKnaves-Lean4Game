import Game.Metadata


World "KnightsAndKnaves" 
Level 5

Title "" 

Introduction 
"
Suppose instead, A and B say the following: 
A: All of us are knaves. 
B: Exactly one of us is a knave. 
Can it be determined what B is? Can it be determined what 
C is?
"


Statement
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{h2: B ∈ Knight ∨ B ∈ Knave }
{h3: C ∈ Knight ∨ C ∈ Knave }
{stA : A ∈ Knight  ↔ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave) }
-- exactly one of us is a knave
-- this can be represented as Knave = {A} ∨ Knave = {B} ∨ Knave = {C}
{stB: B ∈ Knight ↔ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knight ∨ A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knight ∨ A ∈ Knight ∧ B ∈ Knight ∧ C ∈ Knave) }
{stBn: B ∈ Knave ↔ ¬ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knight ∨ A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knight ∨ A ∈ Knight ∧ B ∈ Knight ∧ C ∈ Knave) }
  : A ∈ Knave ∧ C ∈ Knight := by

  {
 -- constructor
  have AKnave : A ∈ Knave := by
    by_contra AKnight
    rw [notinright_inleftIff h1 h] at AKnight
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
      rw [inright_notinleftIff h1 h] at AKnave
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
    rw [inleft_notinrightIff h3 h] 
    assumption


  }




example
  --sets
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{h2: B ∈ Knight ∨ B ∈ Knave }
{h3: C ∈ Knight ∨ C ∈ Knave }
{AneB : A≠ B}
{BneC : B≠ C}
{AneC : A≠ C}
-- Knave = {A,B,C} ???
-- similar to previous problem
{stA : A ∈ Knight  ↔ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave) }
{stB : B ∈ Knight ↔ Knave = {A} ∨ Knave = {B} ∨ Knave = {C}}
  : A ∈ Knave ∧ C ∈ Knight := by
    have AKnave : A ∈ Knave := by 
      by_contra AKnight
      have AKnight :=notright_left h1 AKnight
      have := stA.mp AKnight
      exact disjoint h AKnight this.left

    constructor
    assumption
    rcases h2 with BKnight|BKnave
    · have knavesingle := stB.mp BKnight
      cases knavesingle
      · by_contra CKnave
        have CKnave:= notleft_right h3 CKnave
        #check full_singleton 
        exact full_singleton h_1 CKnave AneC.symm
      · cases h_1
        · have := singleton_not_in h_2 BneC.symm
          exact notright_left h3 this
        · #check singleton_not_in
          have := singleton_not_in h_2 AneC
          contradiction
    · by_contra CnKnight
      have CKnave := notleft_right h3 CnKnight
      have AKnight := stA.mpr (by constructor ; assumption ; constructor ; assumption ; assumption)
      exact disjoint h AKnight AKnave

Conclusion 
"
"

