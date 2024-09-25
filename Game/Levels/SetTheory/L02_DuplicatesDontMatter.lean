import Game.Metadata


World "SetTheory" 
Level 2

Title "Duplicates Dont Matter" 

Introduction 
"
"
#check Set.mem_def
Statement 
  :({A,A} = ({A} : Set Type))  := by

  {
    #check Membership
    apply Set.ext_iff.mpr
    intro x
    constructor
    · intro ele
      cases ele
      · rw [h]
        rfl
      · assumption
    · intro ele
      cases ele
      --exact Set.mem_insert _ _
      exact Set.mem_insert A ({A} : Set Type)
      
      
  }





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

--NewTactic 
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

