import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Basic

        #check Finset.singleton_subset_iff
        #check Finset.subset_of_eq
#check Finset.mem_singleton
#check Finset.mem_singleton_self
theorem card_eq {Normal : (Finset K)} (h : Normal.card =1) (ANormal : A ∈ Normal) ( BNormal : B ∈ Normal) : A=B := by 
  have := Nat.le_of_eq h
  rw [Finset.card_le_one_iff] at this
  exact this ANormal BNormal

theorem full  
{S : Finset K} 
{B : K}
(AinS: A ∈ S)
(One : S.card =1)
(AneB : A ≠ B)
: B ∉ S := by {
  by_contra BinS
  exact AneB (card_eq One AinS BinS)
}

theorem is_singleton {A : K} {S : Finset K}
(AinS : A ∈ S) (OneS : S.card = 1 )
: S={A} := by 
  have OneS2 := Finset.card_eq_one.mp OneS
  #check Finset.nontrivial_iff_ne_singleton
  #check Finset.Nontrivial
  by_contra ne_singleton
  push_neg at ne_singleton
  have := (Finset.nontrivial_iff_ne_singleton AinS).mpr ne_singleton
  unfold Finset.Nontrivial at this
  unfold Set.Nontrivial at this
  have ⟨x,hx,y,hy,xney⟩ := this 
  #check full
  #check card_eq
  #check Finset.nontrivial_iff_ne_singleton 
  exact xney (card_eq OneS hx hy )

#check is_singleton
-- is single_iff_exists and singleton_iff_card_eq_one pointless?? i probably only would need the forward direction in a problem , also the assumption ruins the original point of the lemma which was built on an error in my reasoning.
theorem singleton_iff_exists {S : Finset K}
{B : K} (BinS : B ∈ S): S={B} ↔ ∃x, S={x} := by 
  constructor
  · intro singleton
    use B 
  · intro exist
    have ⟨x,hx⟩ := exist  
    rw [hx] at BinS  
    have Beqx := Finset.mem_singleton.mp BinS
    rw [Beqx]
    assumption
theorem singleton_iff_card_eq_one {S : Finset K}
{B : K}
{all : ∀(x:K), x=B}
: S={B} ↔ S.card=1 := by 
  constructor
  · intro singleton
    rw [Finset.card_eq_one]
    #check Classical.not_forall_not
    use B
  · intro One
    rw [Finset.eq_singleton_iff_unique_mem] 
    sorry

theorem full_singleton  
{S : Finset K} 
{B : K}
(singleton : S={B})
(AinS: A ∈ S)
(AneB : A ≠ B)
: False := by {
   rw [singleton] at AinS 
   have AeqB := Finset.mem_singleton.mp AinS
   contradiction
   
   --exact AneB (by )
---
  --#check Finset.eq_singleton_iff_unique_mem
  --have exist: ∃x, S={x} := by use B
  --rw [Finset.card_eq_one.symm] at exist 
  --#check card_eq
  --exact AneB (card_eq exist AinS

  --exact AneB (card_eq (by rw [Finset.card_eq_one] ; use B) AinS (by rw [singleton] ; exact Finset.mem_singleton.mpr rfl))

  --by_contra BinS
  --exact AneB (card_eq One AinS BinS)
}

theorem not_in_of_singleton  
{S : Finset K} 
{B : K}
(singleton : S={B})
(AneB : A ≠ B)
: A ∉ S := by {
  by_contra AinS
  exact full_singleton singleton AinS AneB
  --exact AneB (card_eq (by rw [Finset.card_eq_one] ; use B) AinS (by rw [singleton] ; exact Finset.mem_singleton.mpr rfl))

  --by_contra BinS
  --exact AneB (card_eq One AinS BinS)
}


theorem mem_of_eq_singleton {S : Finset K} {A : K} (h : S={A}) : A ∈ S := by 
  symm at h
  have := Finset.subset_of_eq h
  exact Finset.singleton_subset_iff.mp this

-- A ∈ S and S.card=1 , so S={A}
theorem eq_singleton_card_one {A : K} {S : Finset K } 
(singleton : S={A}) : S.card=1 := by 
  #check Finset.subset_of_eq
  #check Finset.card_le_of_subset
  #check Finset.card_eq_of_equiv
  --have := Finset.card_eq_of_equiv (by exact Equiv.setCongr singleton )
  have Sin := Finset.subset_of_eq singleton
  have Ain := Finset.subset_of_eq singleton.symm
  have Sless := Finset.card_le_of_subset Sin
  have Aless := Finset.card_le_of_subset Ain

  exact (Nat.le_antisymm Aless Sless).symm


  --rw [(Finset.nontrivial_iff_ne_singleton).symm] at ne_singleton
  
#check Insert
#check Set.univ
theorem forward {A B C : K} (all : ∀ (x : K), x = A ∨ x = B ∨ x = C) : (Set.univ)  = ({A,B,C} : Set K) := by 
  #check Set.univ_subset_iff
  #check Set.eq_univ_of_univ_subset
  apply Set.eq_of_subset_of_subset
  · intro x
    intro xU
    exact all x

  -----
   --- exact fun ⦃a⦄ a_1 => all a

  · 
    intro x
    intro xABC
    exact trivial

  -------
    --- exact fun ⦃a⦄ a => trivial
theorem backward  {A B C : K} (h : (Set.univ)  = ({A,B,C} : Set K) ):  ∀ (x : K), x = A ∨ x = B ∨ x = C:= by 
  intro x
  have : x ∈ Set.univ := by exact trivial
  rw [h] at this
  exact this

theorem univ_or  {A B C : K} :  (Set.univ)  = ({A,B,C} : Set K)  ↔  ∀ (x : K), x = A ∨ x = B ∨ x = C:= by 
  constructor
  exact fun a x => backward a x
  #check forward
  exact forward

theorem card_eq_one_iff_singletons 
{A B C : K} {S : Finset K} (h : S.Nonempty)
(all : ∀(x : K), x = A ∨ x = B ∨ x = C)
--(AneB : A ≠ B)
--(BneC : B ≠ C)
--(AneC : A ≠ C)
: S.card =1 ↔  S = {A} ∨ S = {B} ∨ S = {C}
  := by 
  constructor
  · intro OneS
    unfold Finset.Nonempty at h
    have ⟨x,hx⟩ := h 
    have Ors := all x
    cases Ors
    · rw [h_1] at hx
      -- A ∈ S and S.card=1 , so S={A}
      #check full_singleton
      have := Finset.card_eq_one.mp OneS
      left
      exact is_singleton hx OneS
    · cases h_1
      -- identical reasoning
      · right
        left
        rw [h_2] at hx
        exact is_singleton hx OneS 

      · right
        right
        rw [h_2] at hx
        exact is_singleton hx OneS 
         
  · intro singletons
    cases singletons
    ·  
      exact eq_singleton_card_one h_1
    · cases h_1
      · exact eq_singleton_card_one h_2
      · exact eq_singleton_card_one h_2

theorem card_eq_one_iff_singletons_univ (A B C : K) {S : Finset K} (h : S.Nonempty)
(U : (Set.univ)  = ({A,B,C} : Set K))
--(all : ∀(x : K), x = A ∨ x = B ∨ x = C)
--(AneB : A ≠ B)
--(BneC : B ≠ C)
--(AneC : A ≠ C)
: S.card = 1 ↔ S = {A} ∨ S = {B} ∨ S = {C} := by  
  have all := univ_or.mp U
  exact card_eq_one_iff_singletons h all 

-- can use to intuitively explain other things like x ∈ {A} means x=A etc.. start from it and then say more generally ...
-- mem1_iff_or for x ∈ {A}
-- mem2_iff_or for x ∈ {A,B}
theorem mem_iff_or (x : K) (h : x ∈ ({A,B,C} : Set K)) : x = A ∨ x =B ∨ x = C := by unfold Set at h ; exact h

theorem one_in_of_card_eq_one {A B C : K} {S : Finset K} {nonemp : S.Nonempty}  (U : Set.univ = ({A,B,C} : Set K)) (h : S.card = 1) 
(AneB : A ≠ B)
(BneC : B ≠ C)
(AneC : A ≠ C)
: A ∈ S ∧ B ∉ S ∧ C ∉ S ∨ A ∉ S ∧ B ∈ S ∧ C ∉ S ∨ A ∉ S ∧ B ∉ S ∧ C ∈ S := by 

  rw [card_eq_one_iff_singletons_univ A B C nonemp U ] at h  
  cases h
  · left
    constructor
    · exact mem_of_eq_singleton h_1
      
    · constructor
      ·         exact not_in_of_singleton h_1 (AneB.symm) 
      · exact not_in_of_singleton h_1 (AneC.symm)

  -- similarly
  · cases h_1
    · right
      left 
      constructor
      · exact not_in_of_singleton h AneB 
      · constructor
        · exact mem_of_eq_singleton h
        · exact not_in_of_singleton h BneC.symm

    · right
      right
      constructor
      · exact not_in_of_singleton h AneC
      · constructor
        · exact not_in_of_singleton h BneC
        · exact mem_of_eq_singleton h

  
-- try using Set.univ as an axiom instead and see if there are any advantages
#check Finset.univ
theorem univ_iff_all {A B C : K} {inst : Fintype K} {inst2 : DecidableEq K}  : Finset.univ = ({A,B,C} : Finset K) ↔  ∀ (x : K), x = A ∨ x = B ∨ x = C:= by 
--  #check Finset.univ
--  #check Finset.toSet Finset.univ
--  #check Finset.coe_inj
--  #check ↑(Finset.univ)
--  rw [Finset.coe_inj.symm]
--  #check Finset.coe_inj
--  #check Finset.toSet
--  have : Finset.univ = {A,B,C} ↔ Set.univ = {A,B,C} := by 
--    constructor
--    · intro Fu
--      rw [Fu]
--    · sorry


    --apply?

  constructor
  · intro U
    intro x
    #check Finset.mem_univ
    have : x ∈ Finset.univ := Finset.mem_univ x 
    rw [U] at this
    #check instDecidableEqBool
    #check Finset.mem_insert_of_mem
    #check Finset.mem_insert
    rw [Finset.mem_insert] at this
    rw [Finset.mem_insert] at this
    rw [Finset.mem_singleton] at this
    assumption
  · intro U
    apply Finset.ext
    intro a
    constructor
    · intro aU
      cases U a
      · rw [h]
        exact Finset.mem_insert_self A {B, C}
      · cases h
        · rw [h_1]  
          #check Finset.mem_insert_of_mem
          apply Finset.mem_insert_of_mem
          exact Finset.mem_insert_self B {C}
        · rw [h_1]
          apply Finset.mem_insert_of_mem
          apply Finset.mem_insert_of_mem
          exact Finset.mem_singleton.mpr rfl

    · exact fun a_1 => Finset.mem_univ a




