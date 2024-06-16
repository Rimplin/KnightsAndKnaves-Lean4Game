import Game.Metadata

open Set

variable {K : Type}

World "SetTheoryLemmas"
Level 1

Title "Intro"

Introduction "Hi"

Statement memleft_empty_inter (A:Set K) (B: Set K)
(h: x ∈ A) (l: A ∩ B = ∅)
  : x ∉ B := by
  {
    intro h2
    have contr:= mem_inter h h2
    rw [l] at contr 
    contradiction
  }





Conclusion "."

/- Use these commands to add items to the game's inventory. -/


NewTactic intro contradiction 
NewDefinition
--NewDefinition mem_inter_iff
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
/-- asdf -/
TheoremDoc Set.mem_inter as "mem_inter" in "Set"
NewTheorem Set.mem_inter
