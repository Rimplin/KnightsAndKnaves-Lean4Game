import Game.Metadata

World "KnightsAndKnaves2"
Level 1

Title "Intro"

Introduction 
"
A ⇔ (B ∧ C)
B ⇔ (C ∧ ¬A)
A: B is a knight and C is a knight.
B: C is a knight and A is a knave.
"

Statement {A B C : Prop}
{stA : A ↔ (B ∧ C)}
{stB : B ↔ (C ∧ ¬A)} 
: ¬A ∧ ¬B ∧ ¬C := by 
  have nA : ¬A := by 
    intro hA 
    have BC := stA.mp hA
    have CnA := stB.mp BC.left
    exact CnA.right hA
  have nC : ¬C := by 
    intro hC 
    have hB := stB.mpr ⟨hC,nA⟩ 
    have hA := stA.mpr ⟨hB,hC⟩ 
    contradiction

  simp [nC] at stB 
  exact ⟨nA,stB,nC⟩ 

-- develop tactic if x in knight then x not in knave
  -- x says y is a knight
  -- y says that x and y are of different type

/- conventions
for implications, a ' would mean the conclusion of it
-/
  -- maybe do Knights and Knaves thing as inductive type...
  /-
  inhabitant
  | Knight
  | Knave
  -/
