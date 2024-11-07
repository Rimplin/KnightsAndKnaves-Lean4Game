import Game.Metadata


World "KnightsAndKnaves2" 
Level 5

Title "" 

Introduction 
"
"
/-
A ⇔ (¬C  ¬B)
B ⇔ (A ⇔ ¬C)
A: If C is a knave, then B is a knave.
B: A is a knight, if and only if C is a knave.

A is a knave.
B is a knight.
C is a knave. 

A, C knight
B knave
-/
#check imp_true_iff
#check true_implies
Statement {A B C : Prop}
{stA : A ↔ (¬C → ¬B)}
{stAn : ¬A ↔ ¬(¬C → ¬B)}
{stB : B ↔ (A ↔ ¬C)}
{stBn : ¬B ↔ ¬(A ↔ ¬C)}
: A ∧ ¬B ∧ C := by 
  have hC : C := by 
    by_contra nC 
    simp only [nC,not_false_eq_true,true_implies] at stA 
    --nth_rw 1 [stA] at stB
    simp [nC] at stB
    rw [stB] at stA
    #check iff_not_self
    apply iff_not_self
    exact stA

  simp [hC] at stA 
  simp [hC,stA] at stB
  -- done
  simp [*]



--A ⇔ (¬C  ¬B)
--B ⇔ (¬A  C)
--A: If C is a knave, then B is a knave.
--B: If A is a knave, then C is a knight.
-- translate implications to or,and expressions
example {A B C : Prop}
{stA : A ↔ (¬C → ¬B)}
{stAn : ¬A ↔ ¬(¬C → ¬B)}
{stB : B ↔ (¬A → C)}
{stBn : ¬B ↔ ¬(¬A → C)}
: A ∧ B ∧ C := by 

  have hA : A := by 
    by_contra nA
    have CB := stAn.mp nA 
    simp [not_imp] at CB 
    have cont := stB.mp CB.right
    simp [nA] at cont
    exact CB.left cont

  have : ¬ A → C := by simp [hA] 
  have hB :=  stB.mpr this 
  simp [hA,hB] at stA
  --done
  sorry

--A ⇔ (B ∧ ¬C)
--B ⇔ (¬C ⇔ ¬A)
example {A B C : Prop}
{stA : A ↔ (B ∧ ¬C)}
{stAn : ¬A ↔ ¬(B ∧ ¬C)}
{stB : B ↔ (¬C ↔ ¬A)}
{stBn : ¬B ↔ ¬(¬C ↔ ¬A)}
: False := by 
-- getting nA
  rw [stB] at stA 
  have : ((¬C ↔ ¬A) ∧ ¬C) → ¬A := by 
    intro ⟨ACiff,nC⟩  
    rw [ACiff] at nC
    assumption
  have := Implies.trans stA.mp this   
  #check imp_not_self
  have nA : ¬A := by 
   intro a 
   exact (this a) a

  have BC := stAn.mp nA 
  rw [not_and_or] at BC
  simp at BC
  -- do cases then done.. ez, but similar to other levels. want to reason with implications and not or,and expressions.
  sorry


-- cant solve idk why
example {A B C : Prop}
{stA : A ↔ (¬C → ¬B)}
{stAn : ¬A ↔ ¬(¬C → ¬B)}
{stB : B ↔ (A ↔ ¬C)}
{stBn : ¬B ↔ ¬(A ↔ ¬C)}
: False := by 
  have hB : B := by 
    by_contra nB
    have AsameC := stBn.mp nB 
    rw [not_iff] at AsameC 
    have stAn2 := stAn
    rw [AsameC] at stAn2
    rw [not_imp] at stAn2
    simp at stAn2
     
    have hC := Function.mt stAn2 nB
    simp at hC 
    have hA := (not_iff_not.mp AsameC).mpr hC 
    simp [hA,nB,hC] at * 
    sorry
  have nB : ¬B := by 
    intro hB
    have AdiffC := stB.mp hB 
    rw [AdiffC] at stA
    have := stA.mp 
    #check and_imp
    rw [and_imp.symm] at this
    simp at this
    have := (Function.mt this)
    simp at this
    have hC := this hB

    sorry
  sorry

Conclusion 
"
"
