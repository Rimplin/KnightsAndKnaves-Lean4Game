import Game.Metadata

World "KnightsAndKnavesLemmas"
Level 7

Title "If you're not a knave, then the only option left is a knight."

Introduction 
"
You are either a knight or a knave (`h`). If you are not a knave (`h'`), then the only option left is being a knight.

In other words, 
"

Statement
{Knight : Finset Inhabitant } {Knave : Finset Inhabitant}
{inst : DecidableEq Inhabitant}
{h : Knight ∩ Knave = ∅ }
(h' : ¬ (B ∈ Knave))
(h'' : B ∈ Knight ∨ B ∈ Knave)
  :  B ∈ Knight := by
{
  -- use this instead?
  exact notright_left h'' h'
  --exact notinright_inleft h'' h'
}
-- use this exercise to introduce disjucntive syllogism and say that this reasoning is true in general(if needed by future levels).

  -- second approach, direct
  --have h' := eq_false h'
  --rw [h'] at h1
  --simp at h1
  --assumption

Conclusion 
"
"

/-
@[inherit_doc] infixr:35 " /\\ " => And
@[inherit_doc] infixr:35 " ∧ "   => And
@[inherit_doc] infixr:30 " \\/ " => Or
@[inherit_doc] infixr:30 " ∨  "  => Or
@[inherit_doc] notation:max "¬" p:40 => Not p

@[inherit_doc] infix:20 " ↔ "   => Iff

@[inherit_doc] infix:50 " ∈ " => Membership.mem
/-- `a ∉ b` is negated elementhood. It is notation for `¬ (a ∈ b)`. -/
notation:50 a:50 " ∉ " b:50 => ¬ (a ∈ b)
-/
