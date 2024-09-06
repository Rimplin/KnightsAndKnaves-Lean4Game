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
--fintype lean 4 at DuckDuckGo
--https://start.duckduckgo.com/lite/
--
--Defining a Finset in Lean4 - Proof Assistants Stack Exchange
--https://proofassistants.stackexchange.com/questions/4171/defining-a-finset-in-lean4
--
--Mathlib.Data.Finset.Basic
--https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Basic.html#Finset
--
--Mathlib.Data.Fintype.Basic
--https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Fintype/Basic.html#Fintype
--
--Mathlib.Data.Fintype.Card
--https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Fintype/Card.html
--
--Mathlib.Data.Fintype.Card
--https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Fintype/Card.html#Fintype.card
--
--Mathlib.Data.Fintype.Card
--https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Fintype/Card.html#Fintype.card

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

#check eq_true


