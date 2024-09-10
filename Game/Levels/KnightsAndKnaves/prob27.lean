import Game.Metadata
-- problem 27
-- in this problem, we cannot know what `A` is, should this be demonstrated in a level? some helpful lessons are present.

-- let's try cardinality formalization
#check Function.Bijective
#check Function.Bijective

-- use this instead of whatever was being used
--1. Finset.card_insert_of_not_mem.{u_1} {α : Type u_1} {s : Finset α} {a : α} [inst✝ : DecidableEq α] (h : a ∉ s) :
--     (insert a s).card = s.card + 1
#check Finset.card_insert_of_not_mem
#check Finset.card_le_one_iff

#check Inter
#check Finset.image_biUnion_filter_eq
---
example
  --sets
  [inst : DecidableEq K]
  (Knight : Finset K ) (Knave : Finset K)
--  (hK : Finset Knight)
(h : Knight ∩ Knave = ∅ )
(h1 : Xor' (A ∈ Knight) (A ∈ Knave) ) 
(h2: Xor' (B ∈ Knight)  (B ∈ Knave) )
(h3: Xor' (C ∈ Knight)  (C ∈ Knave) )
(stB : (B ∈ Knight) → (A ∈ Knight →
  (A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knight) ) )
(stBn : (B ∈ Knave) → (A ∈ Knight → ¬ (
  (A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knight)) ) )
(stC : ( C ∈ Knight → B ∈ Knave) )
(stnC : ( C ∈ Knave → B ∈ Knight) )

  : B ∈ Knave ∧ C ∈ Knight
  := by 

    have : B ∈ Knight ∧ C ∈ Knave ∨ B ∈ Knave ∧ C ∈ Knight := by 
      cases h3
      exact Or.inr (⟨stC h_1.left ,h_1.left⟩ )
      exact Or.inl (⟨stnC h_1.left ,h_1.left⟩ )


    rcases this with ⟨BKnight,CKnave⟩|⟨_,_⟩ 
    · have BKnight := eq_true BKnight
      have CKnave := eq_true CKnave
      simp [BKnight,CKnave] at stB
      -- need to get BnKnave from BKnight and so on.... include these in the world
      --rw [true_implies] at stB
      sorry
    · exact ⟨left,right⟩ 


#check XorToOr
-- newformalization
example
  --sets
  (Knight : Set K ) (Knave : Set K)
(h : Knight ∩ Knave = ∅ )
(h1 : A ∈ Knight ∨ A ∈ Knave ) 
(h2: B ∈ Knight ∨ (B ∈ Knave) )
(h3: C ∈ Knight ∨ C ∈ Knave )
(stB : (B ∈ Knight) ↔ (A ∈ Knight ↔
  (A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knight) ) )
--(stBn : (B ∈ Knave) → (A ∈ Knight → ¬ (
--  (A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knight)) ) )
(stC : ( C ∈ Knight ↔ B ∈ Knave) )
--(stnC : ( C ∈ Knave → B ∈ Knight) )

  : B ∈ Knave ∧ C ∈ Knight := by 
  -- formalizing solution from book
  -- statement of C implies that B and C are different type
  have : B ∈ Knight ∧ C ∈ Knave ∨ B ∈ Knave ∧ C ∈ Knight := 
    by
    have COr := h3
    cases h3
    -- C Knight
    · have := stC.mp h_1
      right
      constructor
      assumption ; assumption
    -- C Knave
    · rw [not_iff_not.symm] at stC
      rw [NotKnight_KnaveIff h COr] at stC
      have := stC.mp h_1
      rw [NotKnave_KnightIff h h2] at this
      left
      constructor
      assumption; assumption
  cases h1
  · sorry
  · have distrib:= And.intro h_1 this
    #check and_or_left
    rw [and_or_left] at distrib  
    sorry

  cases this 
  · 
    have AIff := stB.mp h_1.left
    
    have : A ∈ Knight → A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knave := by
      intro h'
      have main := h'
      rw [AIff] at h'
      rw [Knave_NotKnightIff h h1] at h'
      simp[main] at h'
      constructor 
      #check eq_true
      #check of_eq_true
      assumption
      assumption
      
  
    -- simplify AIff
    
    have :  (A ∈ Knight ↔ A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knave ∨ A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave ∨ A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knight) ↔ (A ∈ Knight ↔ A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knave) := by 
      constructor 
      · intro h'
        constructor 
        · intro AK
          sorry
        · sorry
      ·  sorry
    sorry

  · assumption
  --have AOr := h1
  --cases h1
  --· cases h2 
  --  · rw [stB.mp h_2] at h_1
  --    cases h_1
  --    · have := Set.mem_inter h_2 h_3.right.left 
  --      rw [h] at this
  --      contradiction
  --    · cases h_3
  --      · rw [stB] at h_2 
  --        rw [not_iff_not.symm] at h_2
  --        push_neg at h_2
  --        rw [Knave_NotKnightIff h AOr] at h_1
  --        have := h_2.mp h_1.left
  --        rw [NotKnight_KnaveIff h AOr] at h_1
  --        exfalso
  --        exact (this.right.left h_1.left h_1.right.left) h_1.right.right 
  --      · constructor
  --        exact h_1.right.left
  --        exact h_1.right.right
  --    --rw [stC] at h_1
  --    --simp at h_1
  --      
  --  · have := stC.mpr h_2
  --    constructor
  --    assumption ; assumption
  --· rw [stC]
  --  simp
  --  sorry




example
  --sets
  [inst : DecidableEq K]
  (Knight : Finset K ) (Knave : Finset K)
(h : Knight ∩ Knave = ∅ )
(h1 : A ∈ Knight ∨ A ∈ Knave ) 
(h2: B ∈ Knight ∨ (B ∈ Knave) )
(h3: C ∈ Knight ∨ C ∈ Knave )
(stB : (B ∈ Knight) ↔ (A ∈ Knight ↔
  (A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knight) ) )
--(stBn : (B ∈ Knave) → (A ∈ Knight → ¬ (
--  (A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knight)) ) )
(stC : ( C ∈ Knight ↔ B ∈ Knave) )
--(stnC : ( C ∈ Knave → B ∈ Knight) )

  : B ∈ Knave ∧ C ∈ Knight := by 
    --Nat.le_of_eq a
    have : Finset.card (Knight) = 1 := by sorry
    have : Finset.card (Knight) ≤ 1 := by exact Nat.le_of_eq this
    #check eq_or_lt_of_le
    #check eq_iff_le_not_lt
    #check Finset.card_le_one_iff
    --rw [Nat.le_of_eq] at this
    -- this is what it means to have cardinality one
    rw [Finset.card_le_one_iff] at this
     
#check ({1,2} : Multiset ℕ)

--variable (K : Type)
--variable (A B C : K)
theorem perm : ({A,B,C}:Set K) = ({C,A,B}:Set K) := by 
  
  apply Set.ext_iff.mpr
  intro x
  constructor 
  · intro h
    refine Set.mem_insert_iff.mpr ?mp.a
    cases h 
    · right
      rw [h_1.symm] 
      exact Set.mem_insert x {B}
    · cases h_1
      · right
        exact Set.mem_insert_of_mem A h
      · left 
        exact h
   -- apply? 
  · --#check Set.insert
    intro h
    refine Set.mem_insert_iff.mpr ?mpr.a
    cases h
    · right
      exact Set.mem_insert_of_mem B h_1
    · cases h_1
      · left
        assumption
      · right
        rw [Set.mem_singleton_of_eq h] 
        exact Set.mem_insert B {C}


-- newformalization
example
  --sets
(Knight : Set K ) 
(hK : Finset Knight)
  (Knave : Set K)
(h : Knight ∩ Knave = ∅ )
(h1 : A ∈ Knight ∨ A ∈ Knave ) 
(h2: B ∈ Knight ∨ (B ∈ Knave) )
(h3: C ∈ Knight ∨ C ∈ Knave )
(
stB : 

(B ∈ Knight) ↔ 
  (A ∈ Knight 
    ↔ ( (Finset.card hK) = 1)
    --(A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knight) 
  ) 
  )

(
stB' : 

(B ∈ Knight) ↔ 
  (A ∈ Knight 
    ↔ ( Knight= {A} ∨ Knight = {B} ∨ Knight = {C})
    --(A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knight) 
  ) 
)
--(stBn : (B ∈ Knave) → (A ∈ Knight → ¬ (
--  (A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knight)) ) )
(stC : ( C ∈ Knight ↔ B ∈ Knave) )
--(stnC : ( C ∈ Knave → B ∈ Knight) )

(ne : A ≠ B )
  : B ∈ Knave ∧ C ∈ Knight := by 
    --squeeze_scope
  --simp at stB'
   
  have AOr := h1
  have : B ∈ Knight ∧ C ∈ Knave ∨ B ∈ Knave ∧ C ∈ Knight := 
    by
    have COr := h3
    cases h3
    -- C Knight
    · have := stC.mp h_1
      right
      constructor
      assumption ; assumption
    -- C Knave
    · rw [not_iff_not.symm] at stC
      rw [NotKnight_KnaveIff h COr] at stC
      have := stC.mp h_1
      rw [NotKnave_KnightIff h h2] at this
      left
      constructor
      assumption; assumption

  cases this 
  · cases h1
    · have := stB'.mp h_1.left
      have this2 := this.mp h_2
      simp[h_1.left,h_2] at this2
      cases this2 
      · rw [h_3] at h_1
        -- from h_1 B=A but we also know B≠A. so we can conclude False closing the goal.
        have hl := h_1.left

        #check Multiset.mem_singleton
        #check Finset.eq_of_mem_singleton
        have AeqB:= (Set.eq_of_mem_singleton hl).symm

        contradiction
      · cases h_3
        · rw [h_4] at h_2 
          have AeqB := Set.eq_of_mem_singleton h_2
          contradiction
        · have h_5 := h_4.symm
            
          --h_5 : {C} = Knight
          #check Set.eq_singleton_iff_unique_mem
          rw [Set.eq_singleton_iff_unique_mem] at h_4
          have c1 := h_4.left
          have c2 := h_1.right
          rw [Knight_NotKnaveIff h h3] at c1
          contradiction
    · -- A is a knave but the right hand of the iff in stB' is true so contradiction
      --#check Set.mem_sub
      have := stB'.mp h_1.left
      rw [not_iff_not.symm] at this
      rw [Knave_NotKnightIff h AOr] at h_2
      have this2 := this.mp h_2
      push_neg at this2
      -- we have Knight = {B} (prove it) and its negation, contradiction
      -- knight subset of {A,B,C}
      have Ksub: Knight ⊆ {A,B,C} := by apply?
      #check Set.subsingleton_or_nontrivial 
        
      have cKnave := h_1.right
      rw[Knave_NotKnightIff h h3] at cKnave
      #check Set.subset_insert_iff_of_not_mem

--1. Set.subset_insert_iff_of_not_mem.{u} {α : Type u} {a : α} {s t : Set α} (ha : a ∉ s) : s ⊆ insert a t ↔ s ⊆ t
      have : Knight ⊆ insert A {B,C} ↔ Knight ⊆ {B,C} := Set.subset_insert_iff_of_not_mem h_2
      #check Set.subset_singleton_iff_eq
      --#check Set.order
      --have perm: {A,B,C} ⊆ {C,A,B} := by sorry
      rw [this] at Ksub
      #check perm
      rw [Set.pair_comm] at Ksub
      have sm: Knight ⊆ insert C {B} ↔ Knight ⊆ {B} := Set.subset_insert_iff_of_not_mem cKnave
      rw [sm] at Ksub
      #check Set.subset_singleton_iff_eq
      rw [Set.subset_singleton_iff_eq] at Ksub
      have : Knight ≠ ∅ := sorry
      cases Ksub
      · contradiction 
      · have := this2.right.left
        contradiction
  · assumption
  --have this2: B ∈ Knight ∧ C ∈ Knave ∨ B ∈ Knave ∧ C ∈ Knight → hK.card  =1 := by {
  --intro 
  --sorry
  --}

  --sorry

example (A : K) (Knight : Set K) (hK : Finset Knight) : Knight = {A} := by sorry
example [DecidableEq K] (Knight : Set K) (hK : Finset Knight) (ne : Finset.Nonempty hK) (hA : A ∈ Knight) (hB : B ∈ Knight): hK.card =2 := by {
  apply Nat.le_antisymm
  · apply? 
  · apply?
}
#check Finset.card_eq_two
#check Finset.card_pos
#check Finset.Nonempty
#check eq_true
#check card_finset_fin_le
#check Finset.card_ne_zero_of_mem
#check Fin





--def A : Person := Person.Knight ∨ Person.Knave
--def B : Person := Person.Knight ∨ Person.Knave
--def C : Person := Person.Knight ∨ Person.Knave

theorem solve_puzzle   (Knight : Set K ) (Knave : Set K)
  (hK : Fintype Knight)
(h : Knight ∩ Knave = ∅ )
(h1 : Xor' (A ∈ Knight) (A ∈ Knave) ) 
(h2: Xor' (B ∈ Knight)  (B ∈ Knave) )
(h3: Xor' (C ∈ Knight)  (C ∈ Knave) )
(stB : (B ∈ Knight) → (A ∈ Knight →
  (A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knight) ) )
(stBn : (B ∈ Knave) → (A ∈ Knight → ¬ (
  (A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knight)) ) )
(stC : ( C ∈ Knight → B ∈ Knave) )
(stnC : ( C ∈ Knave → B ∈ Knight) )

  : B ∈ Knave ∧ C ∈ Knight
 := by

  cases h2 
  · sorry
  · sorry
 -- | Knight := given conditions
 --   contradiction
 -- | Knave := 
 --   -- Case where B is a Knave
 --   have hC : C = Person.Knight, from (iff.mp (propext and_iff_right_iff_imply)) (iff.symm _),

 --   exact ⟨hB, hC⟩,







