import Game.Metadata

World "KnightsAndKnaves2" 
Level 2

Title "" 

/-
wolfram generated
A ⇔ (C ∨ B)
B ⇔ (A ⇔ C)

-/
Introduction 
"
A: C is a knight or B is a knight.

B: A is a knight, if and only if C is a knight.

Everytime you need to assume, and for every bullet point, you would need to use the `have` tactic.

Assuming `¬A`,
- Prove `¬C ∧ ¬B` from `stAn`
- Prove `¬(A ↔ C)` from `stBn`
- Prove `A ↔ C` from `¬A, ¬C`
- Prove `False` from `¬(A ↔ C) , (A ↔ C)`

We have proven `¬A → False` which is `¬¬A` i.e `A`.

Notice that `¬A` means `¬C, ¬B` where ¬B gives that A and C dont have the same type. This is a contradiction of course so the proposition ¬A is not true which means that A is true.  

Now we know A, which gives C ∨ B
¬B means C, and it also means ¬(A ↔ C). But we know A ↔ C from A,C so we get a contradiction.

lets take cases for C ∨ B. Having C gives us (A ↔ C) which gives us B. So we get as a final answer, A ∧ B ∧ C. 
Having B, we get that (A ↔ C) which gives us C. The final answer is A ∧ B ∧ C.

Now we know A,B. From B we get that A ↔ C, which means C.

Now we know A,B,C.
"
Statement {A B C : Prop}
{stA : A ↔ (C ∨ B)}
{stAn : ¬A ↔ ¬(C ∨ B)}
{stB : B ↔ (A ↔ C)}
{stBn : ¬B ↔ ¬(A ↔ C)}
: A ∧ B ∧ C := by 
   
  have stAn2 := stAn
  rw [stB] at stAn 
  rw [not_or] at stAn
  have hA: A := by 
    by_contra nA 
    have ⟨nC,AdiffC⟩ := stAn.mp nA
    rw [not_iff] at AdiffC
    have hC := AdiffC.mp nA 
    exact nC hC
  
  -- explore cases
  -- now we have that C ∨ B. Looking at the case where B is true, doesn't seem to contradict anything and we don't have enough information to make a conclusion. Looking at the case where ¬B is true, we have that C must be true from the C ∨ B,and from stBn we conclude that A,C dont have the same type. So ¬C must be true as well which is a contradiction. 
  have CorB := stA.mp hA 

  -- another strat, cases CorB
  cases CorB
  · simp [h,hA] at stB 
    -- done
    exact ⟨hA,stB,h⟩  
  · simp [hA,h] at stB 
    -- done
    exact ⟨hA,h,stB⟩ 

example {A B C : Prop}
{stA : A ↔ (C ∨ B)}
{stAn : ¬A ↔ ¬(C ∨ B)}
{stB : B ↔ (A ↔ C)}
{stBn : ¬B ↔ ¬(A ↔ C)}
: A ∧ B ∧ C := by 
  have hA : A := by 
    by_contra nA 
    have nCnB := stAn.mp nA 
    push_neg at nCnB
    have nC := nCnB.left
    have : A ↔ C := by 
    -- when proof of something is based on truth table, usually simp can do it
      simp [nA,nC]
      --exact (iff_true_right nC).mpr nA
    have nAiffC := stBn.mp nCnB.right 
    contradiction

  have hB : B := by 
    by_contra nB
    simp [nB] at stA 
    have := stBn.mp nB
    contradiction

  have AiffC := stB.mp hB
  have hC := AiffC.mp hA
  exact ⟨hA,hB,hC⟩ 



/-
wolfram generated
A ⇔ (¬C ∧ B)
B ⇔ (C ⇔ A)
A: C is a knave and B is a knight.
B: C is a knight, if and only if A is a knight.
-/
example {A B C : Prop}
{stA : A ↔ (¬C ∧ B)}
{stAn : ¬A ↔ ¬(¬C ∧ B)}
{stB : B ↔ (C ↔ A)}
{stBn : ¬B ↔ ¬(C ↔ A)}
: ¬A ∧ ¬B ∧ C := by 
  have nA : ¬A := by 
    intro hA 
    have ⟨nC,hB⟩ := stA.mp hA  
    have CiffA := stB.mp hB
    rw [CiffA] at nC
    contradiction
  have CorB := stAn.mp nA 
  rw [not_and_or] at CorB
  simp at CorB
  
  have nB : ¬B := by 
    intro hB 
    have CiffA := stB.mp hB
    simp [hB] at CorB
    rw [CiffA] at CorB 
    contradiction
  have hC : C := by 
    have CA_not_same := stBn.mp nB
    #check not_iff 
    rw [not_iff]at CA_not_same
    rw [CA_not_same.symm] at nA 
    simp at nA
    assumption

  exact ⟨nA,nB,hC⟩ 

--https://philosophy.hku.hk/think/logic/knights.php
-- translation of this puzzle is tricky
--Here is your puzzle:
--
--You have met a group of 3 islanders. Their names are Xavier, Gary, and Alice.
--    Gary says: Alice is my type.   Alice says: Gary never lies.    Gary says: Xavier never lies.
--example
--{Gary Xavier Alice : Prop}
--{stG : Gary ↔ Alice}
--{stA : Alice ↔ Gary}
--{stG2 : Gary ↔ Xavier}

--solution:    A knight or a knave will say they are the same type as a knight. So when Gary says they are the same type as Alice, we know that Alice is a knight.
--    All islanders will call one of their same kind a knight. So when Alice says that Gary is a knight, we know that Gary and Alice are the same type. Since Alice is a knight, then Gary is a knight.
--    All islanders will call one of their same kind a knight. So when Gary says that Xavier is a knight, we know that Xavier and Gary are the same type. Since Gary is a knight, then Xavier is a knight.
--
--For these reasons we know there were no knaves , and the knights were Alice, Xavier, and Gary.
example
  --sets
  {Gary Alice Xavier: Inhabitant}
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{Or : ∀(x :Inhabitant), x ∈ Knight ∨ x ∈ Knave}
{stG1 : Gary ∈ Knight  ↔ (Alice ∈ Knight) }
{stGn1 : Gary ∈ Knave  ↔ (Alice ∈ Knight) }
{stG2 : Gary ∈ Knight  ↔ (Xavier ∈ Knight) }
{stGn2 : Gary ∈ Knave  ↔ (Xavier ∈ Knave) }
{stA : Alice ∈ Knight ↔ (Gary ∈ Knight)}
{stAn : Alice ∈ Knave ↔ (Gary ∈ Knave)} : Gary ∈ Knight ∧ Alice ∈ Knight ∧ Xavier ∈ Knight := by{
  rcases Or Gary with GaryKnight|GaryKnave
  · have AliceKnight:= stG1.mp GaryKnight
    have XavierKnight := stG2.mp GaryKnight
    constructor
    assumption
    constructor
    assumption
    assumption

  · have AliceKnight := stGn1.mp GaryKnave
    have GaryKnight := stA.mp AliceKnight
    exfalso
    exact disjoint h GaryKnight GaryKnave
}

-- tough translation
--https://philosophy.hku.hk/think/logic/knights.php
--Here is your puzzle:
--
--You have met a group of 2 islanders. Their names are Robert and Ira.
--
--    Robert says: Ira is my type.
--    Ira says: Robert is truthful.
--solution:     A knight or a knave will say they are the same type as a knight. So when Robert says they are the same type as Ira, we know that Ira is a knight.
--    All islanders will call one of their same kind a knight. So when Ira says that Robert is a knight, we know that Robert and Ira are the same type. Since Ira is a knight, then Robert is a knight.
--
--For these reasons we know there were no knaves , and the knights were Robert and Ira.
--example
--{Robert Ira : Prop}
example
  {Robert Ira: Inhabitant}
  {Knight : Set Inhabitant} 
  {Knave : Set Inhabitant}
  {h : Knight ∩ Knave = ∅ }
  {Or : ∀(x :Inhabitant), x ∈ Knight ∨ x ∈ Knave}
  {stR : Robert ∈ Knight ↔ Ira ∈ Knight}
  {stRn : Robert ∈ Knave ↔ Ira ∈ Knight}
  {stI : Ira ∈ Knight ↔ Robert ∈ Knight}
  {stIn : Ira ∈ Knave ↔ Robert ∈ Knave} : Robert ∈ Knight ∧ Ira ∈ Knight := by 
    have IraKnight : Ira ∈ Knight := by 
      cases Or Robert
      · exact stR.mp h_1
      · exact stRn.mp h_1
    constructor
    · exact stI.mp IraKnight
    · assumption

Conclusion 
"
"
