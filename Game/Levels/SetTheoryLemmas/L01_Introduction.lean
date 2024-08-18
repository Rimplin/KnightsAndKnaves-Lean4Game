import Game.Metadata
open Set

variable {K : Type}

World "SetTheoryLemmas"
Level 1

Title "Intro"

Introduction "Hi"





variable [IsLeftCancelMul ℤ ]

 example : False := by
   have : (0 : ℤ) * 0 = 0 * 1 → 0 = 1 := mul_left_cancel
   norm_num at this

Conclusion "."

/- Use these commands to add items to the game's inventory. -/


--NewTactic contradiction 
NewDefinition
--NewDefinition mem_inter_iff
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
/-- asdf -/
TheoremDoc Set.mem_inter as "mem_inter" in "Set"
NewTheorem Set.mem_inter
