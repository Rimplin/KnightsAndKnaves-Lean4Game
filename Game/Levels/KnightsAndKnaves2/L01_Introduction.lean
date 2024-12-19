import Game.Metadata

World "KnightsAndKnaves2"
Level 1

Title ""

Introduction 
"
A: B is a knight and C is a knight.

B: C is a knight and A is a knave.

Formally,
```
stA : A ↔ B ∈ Knight ∧ C ∈ Knight
stB : B ↔ C ∈ Knight ∧ A ∈ Knave
```



Using `¬C`, we get `¬C ∨ A` which gives `¬B` using `stBn`.
"

Statement
{A B C : Prop}
{stA : A ↔ (B ∧ C)}
{stAn : ¬A ↔ ¬(B ∧ C)}
{stB : B ↔ (C ∧ ¬A)} 
{stBn : ¬B ↔ ¬(C ∧ ¬A)} 
: ¬A ∧ ¬B ∧ ¬C := by 
  Template

  have nA : ¬A := by 
    Hint
    "
Assuming `A` is true:
- Prove `BC : B ∧ C` from `stA` using `A`
- Prove `CnA : C ∧ ¬A` from `stB` using `B`
- Prove `cont :False` from `A`,`¬A` which is the goal.
    "
    Hole
    intro hA 
    have BC := stA.mp hA
    have CnA := stB.mp BC.left
    exact CnA.right hA

--  Hint
--  "
--  Notice that `C` being true gives us that `C ∧ ¬A` which gives `B`. Having `B` gives `B ∧ C` which gives `A` (from `stA`). Since we already know `¬A`, we reached a contradiction from assuming `C`.
--  "
  have nC : ¬C := by
    Hint
    "
Assuming `C` is true:
- `B` from `stB` using `C ∧ ¬A`
- `A` from `stA` using `B ∧ C`
- `False` from `A`,`¬A`
    "
    Hole
    intro hC
    have hB := stB.mpr ⟨hC,nA⟩
    have hA := stA.mpr ⟨hB,hC⟩
    contradiction

  Hole
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

/- conventions
for implications, a ' would mean the conclusion of it
-/
