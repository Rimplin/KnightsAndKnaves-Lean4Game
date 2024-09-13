import Game.Metadata

#check Finset.mem_def
example
  --sets

  [inst : DecidableEq K]
  (A B C : K)
  (AneB : A ≠ B)
  (BneC : B ≠ C)
  (AneC : A ≠ C)
  (Knight : Set K ) (Knave : Finset K)
  {Normal : Finset K}
{hK : Finset Knight}
{hKn : Finset Knave}
{hN : Finset Normal}
{finKnight : Fintype Knight}
{OneKnight : Finset.card (Set.toFinset Knight) =1 }
{OneKnave : Finset.card Knave =1 }
{OneNormal : Finset.card Normal =1 }

{hKKn : Knight ∩ Knave = ∅ }
{hKN : Knight ∩ Normal = ∅ }
{hKnN : Knave ∩ Normal = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave ∨ A ∈ Normal }
{h2 : B ∈ Knight ∨ B ∈ Knave ∨ B ∈ Normal }
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
    --sorry
    -- have to fix this
    --have KnightSet:=Finset.toSet Knight
    #check Set.toFinset
    --rw [KnightSet] at ANormal
    exact disjoint  hKN AKnight ANormal
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
      --rw [Finset.mem_coe.symm] at ANormal
      --rw [Finset.mem_coe.symm] at BNormal
      -- I have B ∈ Normal, i want B ∈ hK
      -- turning all sets into finset messes up membership...
      --have : B ∈ hK := by sorry
      --have := Finset.mem_def.mp BNormal
      have AeqB:= by exact this ANormal BNormal
      contradiction
    have BNormalKnight:=  Or.symm BKnightNormal
    clear BKnightNormal
    have BKnight := disjunctiveSyllogism BNormalKnight BnNormal
    have CKnave : C ∈ Knave := by 
      rcases h3 with CKnight|CKnaveNormal
      · -- if a set has cardinality one and there are two elements in it then they are equal, make this as its own theorem and use it here instead of reproving  
        have : C ∈ Set.toFinset (Knight) := by exact Set.mem_toFinset.mpr CKnight
        have this2: B ∈ Set.toFinset (Knight) := by exact Set.mem_toFinset.mpr BKnight
        #check Set.mem_toFinset
        have BeqC := card_eq OneKnight this2 this
        contradiction
      · rcases CKnaveNormal with CKnave|CNormal
        · assumption
        · have AeqC := card_eq OneNormal ANormal CNormal
          contradiction 

  have AKnave : A ∈ Knave := by
    cases AKnaveNormal
    assumption
    contradiction

  have BnKnight : B ∉ Knight := by
    intro h
    have := stB h
    contradiction
  have BnKnave : B ∉ Knave := by 
    intro h_1
    have := card_eq OneKnave AKnave h_1
    contradiction
  have := disjunctiveSyllogism h2 BnKnight 
  have := disjunctiveSyllogism this BnKnave 
  
  -- now C is a knight by a similar reasoning... it is the only option left...


