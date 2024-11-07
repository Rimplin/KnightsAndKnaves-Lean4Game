import Game.Metadata

World "KnightsAndKnaves2"
Level 1

Title "Intro"

Introduction 
"
A: B is a knight and C is a knight.

B: C is a knight and A is a knave.

The reasoning that gives us `¬A` is as follows:
Assuming `A` is true:
- `B ∧ C` from `stA` using `A`
- `C ∧ ¬A` from `stB` using `B`
- `False` from `A`,`¬A`.

The reasoning that gives us `¬C` is as follows:
Assuming `C` is true:
- `B` from `stB` using `C ∧ ¬A`
- `A` from `stA` using `B ∧ C`
- `False` from `A`,`¬A`

Using `¬C`, we get `¬C ∨ A` which gives `¬B` using `stBn`.

You have the freedom of doing whatever(or maybe impose something using Template).

use template
"

Statement {A B C : Prop}
{stA : A ↔ (B ∧ C)}
{stAn : ¬A ↔ ¬(B ∧ C)}
{stB : B ↔ (C ∧ ¬A)} 
{stBn : ¬B ↔ ¬(C ∧ ¬A)} 
: ¬A ∧ ¬B ∧ ¬C := by 
  have nA : ¬A := by 
    intro hA 
    have BC := stA.mp hA
    have CnA := stB.mp BC.left
    exact CnA.right hA

--  Hint 
--  "
--  Notice that `C` being true gives us that `C ∧ ¬A` which gives `B`. Having `B` gives `B ∧ C` which gives `A` (from `stA`). Since we already know `¬A`, we reached a contradiction from assuming `C`.
--  " 
  have nC : ¬C := by 
    intro hC 
    have hB := stB.mpr ⟨hC,nA⟩ 
    have hA := stA.mpr ⟨hB,hC⟩ 
    contradiction

  simp [nC] at stB 
  exact ⟨nA,stB,nC⟩ 

example {A B C : Prop}
{stA : A ↔ (B ∧ C)}
{stAn : ¬A ↔ ¬(B ∧ C)}
{stB : B ↔ (C ∧ ¬A)} 
{stBn : ¬B ↔ ¬(C ∧ ¬A)} 
: ¬A ∧ ¬B ∧ ¬C := by 
  rw [stB] at stA 
  have nA : ¬A := by 
    intro hA
    have := stA.mp hA
    exact this.left.right hA
  simp [nA] at stB 
  simp [nA] at stAn
  rw [stB] at stAn
  have nC : ¬C := by 
    intro hC
    have := stAn hC
    contradiction
  simp [nC] at stB 
  exact ⟨nA,stB,nC⟩

-- develop tactic if x in knight then x not in knave
  -- x says y is a knight
  -- y says that x and y are of different type

/- conventions
for implications, a ' would mean the conclusion of it
-/
