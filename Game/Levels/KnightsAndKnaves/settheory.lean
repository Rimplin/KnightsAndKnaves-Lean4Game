import Game.Metadata
import Mathlib.Data.Multiset.Basic

#check ({1,2} : Multiset ℕ)
#check Set.insert
#check mem_iff_or
theorem perm3 : ({A,B,C}:Set K) = ({C,B,A}:Set K) := by 
  apply Set.ext
  intro x 
  constructor 
  · intro xIn
    have :=mem_iff_or.mp xIn
    rw [or_comm] at this
    rw [@or_comm (x=B) _] at this
    rw [or_assoc] at this
    exact this
     
  · intro xIn
    have := mem_iff_or.mp xIn  
    rw [mem_iff_or ] 

    rw [or_comm]  
    rw [@or_comm (x=B) _] 
    rw [or_assoc] 
    assumption

#check Set.pair_comm 
  #check Set.insert_comm
  #check Set.mem_insert
      #check Set.mem_insert_iff

theorem perm2 : ({A,B,C}:Set K) = ({C,B,A}:Set K) := by 
  apply Set.ext_iff.mpr
  intro x
  constructor 
  · intro hx
    cases hx
    · rw [h]
      repeat apply Set.mem_insert_of_mem <;> try apply Set.mem_insert_iff   
      rfl
    · cases h
      · rw [h_1]
        #check Set.mem_insert_of_mem
        #check Set.mem_insert_iff
        --repeat apply Set.mem_insert_of_mem <;> try apply Set.mem_insert_iff ; exact rfl

        repeat rw [Set.mem_insert_iff]
        right
        left
        rfl

       -- repeat rw [ Set.mem_insert_iff] <;> try left; assumption
         
       -- apply Set.mem_insert_of_mem
        --exact rfl
      · rw [h_1]
        repeat rw [Set.mem_insert_iff]
        left
        rfl
  · intro hx
    cases hx
    · repeat rw [Set.mem_insert_iff]
      right
      right
      rw [h]
      rfl

    · cases h
      · rw [h_1]
        repeat rw [Set.mem_insert_iff]
        right
        left
        rfl
      · rw[  Set.mem_singleton_iff ] at h_1
        rw [h_1]
        repeat rw [Set.mem_insert_iff]
        left
        rfl

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
  · 
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



variable (K : Type)
variable (A B C : K)
example : ({A,B,C}:Set K) = ({C,A,B}:Set K) := by 
  
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
  · 
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
