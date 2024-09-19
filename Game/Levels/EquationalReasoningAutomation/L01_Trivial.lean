import Game.Metadata


World "EquationalReasoningAutomation" 
Level 1

Title "trivial" 

Introduction 
"
"

--macro_rules | `(tactic| trivial) => `(tactic| left)
--macro_rules | `(tactic| contradiction) => `(tactic| left)
--macro_rules
--  | `($l:term RXOR $r:term) => `($l && !$r)
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

/-

- `simp`: This tactic simplifies expressions using a set of predefined rewrite rules. More specifically, the rules used are tagged with @[simp] in mathlib. It's especially useful for basic simplifications involving arithmetic, inequalities, and logical connectives.

- `ring`: This tactic is more powerful and is specifically designed for proving equalities in commutative rings. It automatically applies a variety of algebraic properties such as associativity, commutativity, and distributivity to simplify expressions. It's particularly handy when dealing with expressions involving addition and multiplication.


-/

NewTactic trivial ring simp
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq


