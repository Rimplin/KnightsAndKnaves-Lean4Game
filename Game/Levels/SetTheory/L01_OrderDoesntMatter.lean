import Game.Metadata

World "SetTheory" 
Level 1

Title "What is a set?" 

Introduction 
"
A set is a collection of objects. Order doesn't matter in a set, therefore the two sets A,B and B,A are the same. A set is indicate using \\{\\} 

The goal of this level is to prove that order doesn't matter( there will only be a level to show this for sets with two elements, but it can be extended to any number of elements)


"

#check Set.ext_iff
Statement 
  : ({A,B} : Set Type)={B,A} := by

  {
    Hint "Here we use what it means for two sets to be equal. Two sets are equal if they have the same elements. Try `apply Set.ext_iff.mpr` to see what that means"
    apply Set.ext_iff.mpr
    Hint "You can check the theorems tab or hover over the text to see its type. Now you need to prove a for all statement."
    intro x
    constructor
    · intro ele
      rcases ele with xA|xB
      · rw [xA]
        #check Set.mem_insert_iff
        rw [Set.mem_insert_iff]
        right
        rfl
        
      · #check Set.mem_singleton_iff
        rw [Set.mem_singleton_iff] at xB
        rw [xB]
        
        #check Set.mem_def
        #check Set.mem_insert
        --rw [Set.mem_def]
        exact Set.mem_insert B ({A}:Set Type)

      
    · intro ele
      rcases ele with xB|xA
      · rw [xB]
        #check Set.pair_comm 
        #check Set.mem_insert_iff
        rw [Set.mem_insert_iff]
        right
        rfl

        --exact Set.mem_insert B ({A}: Set Type)
      · rw [Set.mem_singleton_iff] at xA
        rw [xA]
        -- use this to make it easier for the user
        -- ⊢ A ∈ {A, B}
        exact Set.mem_insert _ _

  }
#check Multiset
#check Set
#check Set
#check setOf





Conclusion 
"
Long proof wasn't it? You can use the theorem Set.pair_comm
"

/- Use these commands to add items to the game's inventory. -/

--NewTactic 
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq



#check ({1,2} : Multiset ℕ)
#check Set.insert
#check mem_iff_or

#check Set.pair_comm 
  #check Set.insert_comm
  #check Set.mem_insert
      #check Set.mem_insert_iff
-- same proof for perm3 , perm32 but perm32 is a bit cleaner
theorem perm3 : ({A,B,C}:Set K) = ({C,B,A}:Set K) := by 
  apply Set.ext
  intro x 
  constructor 
  · intro xIn
    have := (mem_iff_or A B C x).mp xIn
    rw [or_comm] at this
    rw [@or_comm (x=B) _] at this
    rw [or_assoc] at this
    exact this

  · intro xIn
    have := (mem_iff_or C B A x).mp xIn
    rw [mem_iff_or ] 

    rw [or_comm]  
    rw [@or_comm (x=B) _] 
    rw [or_assoc] 
    assumption
theorem perm32 : ({A,B,C}:Set K) = ({C,B,A}:Set K) := by 
  apply Set.ext 
  intro x
  constructor
  · intro xABC 
    rw [mem_iff_or A B C x] at xABC
    have : x = C ∨ x = B ∨ x = A := by 
      rw [or_comm] at xABC 
      nth_rw 2 [or_comm] at xABC 
      rw [or_assoc] at xABC  
      assumption
    rw [(mem_iff_or C B A x).symm] at this
    assumption

  · intro xCBA 
    rw [mem_iff_or C B A x] at xCBA
    have : x = A ∨ x = B ∨ x = C := by 
      rw [or_comm] at xCBA 
      nth_rw 2 [or_comm] at xCBA 
      rw [or_assoc] at xCBA  
      assumption
    rw [(mem_iff_or A B C x).symm] at this
    assumption

-- long winded
theorem perm322 : ({A,B,C}:Set K) = ({C,B,A}:Set K) := by 
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

#check Multiset
--example  {inst : DecidableEq K} : ({A,B,C}:Finset K) = ({C,B,A}:Finset K) := by 
--  exact?
--  sorry 
example  {inst : DecidableEq K} : ({A,B}:Finset K) = ({B,A}:Finset K) := by 
  exact Finset.pair_comm A B
