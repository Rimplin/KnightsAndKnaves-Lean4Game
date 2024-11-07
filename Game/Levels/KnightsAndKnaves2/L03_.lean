import Game.Metadata


World "KnightsAndKnaves2" 
Level 3

Title ""

Introduction 
"
similar explanation to lvl 2
"
--A ⇔ (¬C ∨ B)
--B ⇔ (¬A ⇔ C)
--A: C is a knave or B is a knight.
--B: A is a knave, if and only if C is a knight.
Statement {A B C : Prop}
{stA: A ↔ (¬C ∨ B)} 
{stAn: ¬A ↔ ¬(¬C ∨ B)} 
{stB: B ↔ (¬A ↔ C)}
{stBn: ¬B ↔ ¬(¬A ↔ C)}
: A ∧ B ∧ ¬C := by 
  have hA : A := by 
    by_contra nA 
    have ⟨hC,nB⟩:= not_or.mp (stAn.mp nA)
    simp at hC
    simp [nA,hC] at stB
    contradiction 
  have nCB := stA.mp hA 
  cases nCB
  · simp [hA,h] at stB 
    sorry
  · simp [hA,h] at stB
    sorry

Conclusion 
"
"
