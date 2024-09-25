import Game.Metadata


World "SetTheory" 
Level 4

Title "Empty Set" 

Introduction 
"
The empty set is defined as the set that has no elements. In other words, 
For any x, x doesn't belong to the empty set. The empty set is denoted ∅
 (x : α) : x ∉ ∅
"

#check Set.empty_def
#check Set.mem_empty_iff_false
#check Set.not_mem_empty
Statement 
  : 2=2 := by

  {
    rfl
  }





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

--NewTactic 
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

