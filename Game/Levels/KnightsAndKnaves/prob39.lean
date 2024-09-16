import Game.Metadata
import Mathlib.Data.Finset.Basic
#check Finset.mem_def


/-
to solve issues, check membership and coercion here:

mathlib4 docs at DuckDuckGo
https://start.duckduckgo.com/lite/?q=mathlib4+docs

Search
https://leanprover-community.github.io/mathlib4_docs/search.html?sitesearch=https%3A%2F%2Fleanprover-community.github.io%2Fmathlib4_docs&q=Finset

Mathlib.Data.Finset.Basic
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Basic.html#Finset

Mathlib.Data.Finset.Basic
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Basic.html#Finset.instMembership

mathlib4/Mathlib/Data/Finset/Basic.lean at c3c78bbdb01c312bd5143e44a38e6cbc8deb4b90 · leanprover-community/mathlib4 · GitHub
https://github.com/leanprover-community/mathlib4/blob/c3c78bbdb01c312bd5143e44a38e6cbc8deb4b90/Mathlib/Data/Finset/Basic.lean#L166-L167

New Tab
about:newtab
-/

-- two approaches:
-- directly as a finset
-- as a set with a fintype instance to enable conversion to finset
#check Set.toFinset
example 
  --sets

  [inst : DecidableEq K]
  (A B C : K)
  (AneB : A ≠ B)
  (BneC : B ≠ C)
  (AneC : A ≠ C)
  (Knight : Finset K ) (Knave : Finset K)
  {Normal : Finset K}
--{hK : Finset Knight}
--{hKn : Finset Knave}
--{hN : Finset Normal}
{finKnight : Fintype Knight}
{finKnave : Fintype Knave}
{finNormal : Fintype Normal}
{OneKnight : Finset.card ( Knight) =1 }
{OneKnave : Finset.card Knave =1 }
{OneNormal : Finset.card Normal =1 }

{hKKn : Knight ∩ Knave = ∅ }
{hKN : Knight ∩ Normal = ∅ }
{hKnN : Knave ∩ Normal = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave ∨ A ∈ Normal }
{h2 : B ∈ Knight ∨ B ∈ Knave ∨ B ∈ Normal }
{h3 : C ∈ Knight ∨ C ∈ Knave ∨ C ∈ Normal}
{stA : A ∈ Knight → (A ∈ Normal) } {stAn : A ∈ Knave → ¬ (A ∈ Normal) }
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
  {

    by_contra AKnight
    have ANormal := stA AKnight
    --sorry
    -- have to fix this
    --have KnightSet:=Finset.toSet Knight
    #check Set.toFinset
    --rw [KnightSet] at ANormal

    -- when knight and normal are finsets,  disjoint doesn't work because it expects sets... lets try to make a disjoint finset version and see if that woudl work...
    exact disjointfinset hKN AKnight ANormal
  }

  -- interesting observation:
  -- for the knight and knave only, all theorems are sets
  -- for the knight knave normal , i need finsets . why not make theorems for knight and knave also finset, model both situations as a finset.
  --rw [NotKnight_KnaveIff] at AnKnight 
  
  have AKnaveNormal := disjunctiveSyllogism h1 AnKnight 

  have AnNormal : A ∉ Normal := by
  {
    by_contra ANormal
    have BnKnave := (Function.mt stBn) (by push_neg; assumption)
    have BKnightNormal : B ∈ Knight ∨ B ∈ Normal := by
      by_contra not
      push_neg at not
      have := And.intro BnKnave not
      --rw [←and_assoc] at this
      --rw [and_comm] at this
      #check not_or
      rw [←not_or] at this
      rw [←not_or] at this
 --     rw [←or_assoc] at this
      -- this : ¬((B ∈ Knave ∨ B ∈ Knight) ∨ B ∈ Normal)

      --this : ¬(B ∈ Knave ∨ B ∈ Knight ∨ B ∈ Normal)

      --rw [or_comm] at this
      --nth_rewrite 1 [or_comm] at this
      --nth_rewrite 1 [or_comm] at this
      -- can't get them to be the same
      --ring_nf at this
      -- this is messy... can't it be cleaner, well i can present it to be clean: the user would have to do this manually using or_comm and or_assoc but the user can tell simp about these two theorems and let simp do the work
      #check this
      #check ¬(B ∈ Knave ∨ B ∈ Knight ∨ B ∈ Normal)
      --have : (B ∈ Knave ∨ B ∈ Knight ∨ B ∈ Normal) ↔ (B ∈ Knight ∨ B ∈ Knave ∨ B ∈ Normal) := by exact?
      rw [or_left_comm] at this
      --simp [or_comm,or_assoc] at h2
      contradiction
      --have : this = ¬h2 := by apply?
     -- simp only [or_comm,or_assoc] at this
      --simp only [or_comm,or_assoc] at h2
      --contradiction 
      --sorry
    have BnNormal : B ∉ Normal := by
    {
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
    }

    have BNormalKnight:=  Or.symm BKnightNormal

    clear BKnightNormal
    have BKnight := disjunctiveSyllogism BNormalKnight BnNormal

    have CKnave : C ∈ Knave := by {
      rcases h3 with CKnight|CKnaveNormal
      · -- if a set has cardinality one and there are two elements in it then they are equal, make this as its own theorem and use it here instead of reproving  
        -- make a theorem memtoFinset
        have : C ∈ Set.toFinset (Knight) := by exact Set.mem_toFinset.mpr CKnight
        have this2: B ∈ Set.toFinset (Knight) := by exact Set.mem_toFinset.mpr BKnight
        #check Set.mem_toFinset
        -- add new assumptions to BKnight, BFinKnight. wouldn't this be too messy?
        --have BeqC := card_eq OneKnight this2 this
        have BeqC := card_eq OneKnight BKnight CKnight
        contradiction
      · rcases CKnaveNormal with CKnave|CNormal
        · assumption
        · have AeqC := card_eq OneNormal ANormal CNormal
          contradiction 
    }
    have CNormal := stCn CKnave
    have AeqC := card_eq OneNormal ANormal CNormal
    contradiction
  }
  have AKnave : A ∈ Knave := by
  {
    cases AKnaveNormal
    assumption
    contradiction

}

  have BnKnight : B ∉ Knight := by
{ 
    intro h
    have := stB h
    contradiction
}


  have BnKnave : B ∉ Knave := by{ 
    intro h_1
    have := card_eq OneKnave AKnave h_1
    contradiction
}

  have := disjunctiveSyllogism h2 BnKnight 
  have BNormal := disjunctiveSyllogism this BnKnave   

  -- now C is a knight by a similar reasoning... it is the only option left...
  -- make the CnKnave proof into a theorem, call it already full
  have  CnKnave : C ∉ Knave := by 
    by_contra CKnave
    have AeqC := card_eq OneKnave AKnave CKnave
    contradiction
  have  CnNormal : C ∉ Normal := by 
    by_contra CNormal
    have AeqC := card_eq OneNormal BNormal CNormal
    contradiction
  cases h3
  · constructor
    assumption
    constructor
    assumption
    assumption
  · cases h
    contradiction
    contradiction

-- this2: B ∈ Set.toFinset (Knight) := by
theorem memToFinset (Knight : Set K ) {finKnight : Fintype Knight} {hK : Finset Knight} (AKnight : A ∈ Knight) : A ∈ (Set.toFinset Knight) := by  
  exact Set.mem_toFinset.mpr AKnight

-- having a knight finset gives problems with membership, so keep it as set and then do Set.toFinset which requires a Fintype instance...(another way without going through Fintype instance??)
#check Membership
#check Finset.instMembershipFinset
theorem memToFinset2 {Knight : Set K } 
(finKnight : Fintype Knight) 
--{hK : Finset Knight} 
(AKnight : A ∈ Knight) 
--[@Finset.instMembershipFinset K] 
: A ∈ (Set.toFinset Knight) := by  
  exact Set.mem_toFinset.mpr AKnight

-- two options
#check Finset.toSet -- natural way
#check Set.toFinset -- needs fintype instance
#check Fintype
example  {Knight : Set K } 
{finKnight : Fintype Knight} 
--{hK : Finset Knight} 
(AKnight : A ∈ Knight) 
--[@Finset.instMembershipFinset K] 
: 2=2 := by 
  have := memToFinset2 finKnight AKnight
  rfl


variable (K : Type)
#check @Set.univ K
#check Set.mem_univ
example (A B C: K) : @Set.univ K = {A,B,C} := by
  apply Set.ext 
  intro x
  constructor
  sorry
  sorry
  --· intro xUniv
  --  by_contra
  --· exact fun a => trivial
