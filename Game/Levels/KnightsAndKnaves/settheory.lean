import Game.Metadata
import Mathlib.Data.Multiset.Basic
#check ({1,2} : Multiset ℕ)

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
