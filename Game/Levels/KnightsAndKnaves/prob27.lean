import Game.Metadata
import Mathlib.Data.Fintype.Card
-- problem 27
-- in this problem, we cannot know what `A` is, should this be demonstrated in a level? some helpful lessons are present.

-- let's try cardinality formalization
#check Function.Bijective
#check Function.Bijective


---
example
  --sets
  (Knight : Set K ) (Knave : Set K)
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

    have : Fintype.card (Knight) = 1 := by sorry

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

  : B ∈ Knave ∧ C ∈ Knight := by 
    --squeeze_scope
  --simp at stB'
   

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
        sorry
      · sorry
    · sorry
  · sorry
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


