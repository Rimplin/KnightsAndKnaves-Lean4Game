import Game.Metadata

World "KnightsAndKnaves2" 
Level 4

Title "" 

Introduction 
"
A: B is a knight or C is a knight.
B: C is a knave, if and only if A is a knave
"
--A ⇔ (B ∨ C)
--B ⇔ (¬C ⇔ ¬A)

example {A B C : Prop}
{stA : A ↔ (B ∨ C)}
{stAn : ¬A ↔ ¬(B ∨ C)}
{stB : B ↔ (¬C ↔ ¬A)}
{stBn : ¬B ↔ ¬(¬C ↔ ¬A)}
: A ∧ B ∧ C := by   
  have hB : B := by 
    by_contra nB
    have CdiffA := stBn.mp nB 
    simp [nB] at stA
    rw [not_iff] at CdiffA
    simp at CdiffA
    rw [CdiffA] at stA
    exact iff_not_self stA

  have CsameA := stB.mp hB
  have BorC : B ∨ C := by left ; assumption 
  have hA := stA.mpr BorC
  rw [not_iff_not] at CsameA
  have hC := CsameA.mpr hA
  --done
  sorry

Conclusion 
"
"
