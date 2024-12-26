import Game.Metadata

World "KnightsAndKnaves2"
Level 1

Title ""

Introduction 
"
`A`: `B` is a knight and `C` is a knight.

`B`: `C` is a knight and `A` is a knave.

"

Statement
{A B C : Prop}
{stA : A ↔ (B ∧ C)}
{stAn : ¬A ↔ ¬(B ∧ C)}
{stB : B ↔ (C ∧ ¬A)}
{stBn : ¬B ↔ ¬C ∨ A}
: ¬A ∧ ¬B ∧ ¬C := by
  Template

  have hnA : ¬A := by
    Hint
    "
Assuming `hA : A`:
- Prove `BC : B ∧ C` from `stA` using `A`
- Prove `CnA : C ∧ ¬A` using `stB` , `BC.left : B`
- Prove `False` using `AKnight : A`,`CnA.right : ¬A`.
    "
    Hole
    intro hA
    have BC := stA.mp hA
    have CnA := stB.mp BC.left
    exact CnA.right hA

  have hnC : ¬C := by
    Hint
    "
Assuming `hC : C`:
- Prove `hB : B` using `stB`, `C ∧ ¬A`
- Prove `hA : A` using `stA` , `B ∧ C`
- Prove `False` from `hA: A`,`hnA : ¬A`
    "
    Hole
    intro hC
    have hB := stB.mpr ⟨hC,hnA⟩
    have hA := stA.mpr ⟨hB,hC⟩
    contradiction

  Hole
  Hint
  "
Using `¬C`, we get `¬C ∨ A` which gives `¬B` using `stBn`.
  "
  have nCorA : ¬C ∨ A := by
      left
      exact hnC
  have hnB := stBn.mpr nCorA
  exact ⟨hnA,hnB,hnC⟩
