import Game.Metadata

example
  --sets

  [inst : DecidableEq K]
  (A B C : K)
  (AneB : A ≠ B)
  (Knight : Set K ) (Knave : Set K)
  {Normal : Finset K}
{hK : Finset Knight}
{hKn : Finset Knave}
{hN : Finset Normal}
{OneKnight : Finset.card hK =1 }
{OneKnave : Finset.card hKn =1 }
{OneNormal : Finset.card Normal =1 }

{hKKn : Knight ∩ Knave = ∅ }
{hKN : Knight ∩ Normal = ∅ }
{hKnN : Knave ∩ Normal = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave ∨ A ∈ Normal }
{h3 : C ∈ Knight ∨ C ∈ Knave ∨ C ∈ Normal}
{stA : A ∈ Knight → (A ∈ Normal) }
{stAn : A ∈ Knave → ¬ (A ∈ Normal) }
{stB : B ∈ Knight → (A ∈ Normal)}
{stBn : B ∈ Knave → ¬(A ∈ Normal)}
{stC : C ∈ Knight → C ∉ Normal}
{stCn : C ∈ Knave → C ∈ Normal}
-- A ∈ Knave → (A ∉ Knight ∧ A ∉ Normal)
--{stB: B ∈ Knight → () }
--{stBn: B ∈ Knave → ¬ () }
: A ∈ Knave ∧ B ∈ Normal ∧ C ∈ Knight := by 
  --have := IfToIff stA stAn
  have AnKnight : A ∉ Knight := by 
    by_contra AKnight
    have ANormal := stA AKnight
    exact disjoint hKN AKnight ANormal
  have AKnaveNormal := disjunctiveSyllogism h1 AnKnight 
  have AnNormal : A ∉ Normal := by
    by_contra ANormal
    have BKnightNormal : B ∈ Knight ∨ B ∈ Normal := sorry
    have BnNormal : B ∉ Normal := by
      by_contra BNormal
       
      have : Finset.card (Normal) ≤ 1 := by exact Nat.le_of_eq OneNormal
       
      rw [Finset.card_le_one_iff] at this
      #check Finset.instCoeTCFinsetSet
      #check Finset.mem_coe
      --have := Finset.mem_coe.mpr hN
      rw [Finset.mem_coe.symm] at ANormal
      rw [Finset.mem_coe.symm] at BNormal
      have AeqB:= by exact this ANormal BNormal
      contradiction
    have BNormalKnight:=  Or.symm BKnightNormal
    clear BKnightNormal
    have BKnight := disjunctiveSyllogism BNormalKnight BnNormal
    have CKnave : C ∈ Knave := by 
      rcases h3 with CKnight|CKnaveNormal
      · -- if a set has cardinality one and there are two elements in it then they are equal, make this as its own theorem and use it here instead of reproving  
        sorry
      · rcases CKnaveNormal with CKnave|CNormal
        · assumption
        · sorry


  sorry


