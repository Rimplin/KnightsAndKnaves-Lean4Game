import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Basic

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

theorem full_singleton  
{S : Finset K} 
{B : K}
(singleton : S={B})
(AinS: A ∈ S)
(AneB : A ≠ B)
: False := by {
  exact AneB (card_eq (by rw [Finset.card_eq_one] ; use B) AinS (by rw [singleton] ; exact Finset.mem_singleton.mpr rfl))

  --by_contra BinS
  --exact AneB (card_eq One AinS BinS)
}



theorem mem_eq_singleton {S : Finset K} {A : K} (h : S={A}) : A ∈ S := by 
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

  --rw [(Finset.nontrivial_iff_ne_singleton).symm] at ne_singleton
  
theorem card_eq_one_iff_singletons {A B C : K} {S : Finset K} {h : S.Nonempty}
(all : ∀(x : K), x = A ∨ x = B ∨ x = C)
(AneB : A ≠ B)
(BneC : B ≠ C)
(AneC : A ≠ C)
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

