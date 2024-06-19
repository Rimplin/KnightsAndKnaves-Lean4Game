import Game.Metadata


World "EquationalReasoningAutomation" 
Level 1

Title "trivial" 

Introduction 
"
"
/-
macro_rules | `(tactic| trivial) => `(tactic| left)
macro_rules | `(tactic| trivial) => `(tactic| assumption)
example (h : P) : P ∨ Q := by {
  repeat trivial

  --exact Or.inl h
}

extending automations, metaprogramming
-/
Statement 
  : 2=2 := by

  {
    trivial
  }








Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

NewTactic trivial
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq


