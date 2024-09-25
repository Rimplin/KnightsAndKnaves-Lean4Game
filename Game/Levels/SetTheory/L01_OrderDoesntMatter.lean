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

