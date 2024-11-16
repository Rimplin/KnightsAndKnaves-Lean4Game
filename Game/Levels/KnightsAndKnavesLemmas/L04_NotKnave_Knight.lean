import Game.Metadata

World "KnightsAndKnavesLemmas"
Level 7

Title ""

Introduction 
"
Before starting the riddles, some new concepts have to be clarified.
It is obvious that no one can be a knight and a knave at the same time. If some is not a knave then they are a knight.

You need to show that having two sets being disjoint (i.e sharing no common element) and having a common element is a contradiction.

For the contradiction 
This is not an obvious contradiction (like p , ¬p) for the `contradiction` tactic to work. 
Some work needs to be done to get to that point.
We can get that `A ∈ ∅` and we know that
```
Set.not_mem_empty.{u} {α : Type u} (x : α) : x ∉ ∅
```

Hint: the goal is to get something that contradicts not_mem_empty. Since x belong to Knight and Knave then it belongs to their intersection which is equal to the empty set contradiction not_mem_empty. Let's do this step by step. (Make it feel like the player discovered this:
Notice that the only information we can derive is that x is in the intersection. Do we have information about the intersection? Well yes. its empty set so x ∈ empty set. Execute the finishing blow. 
"

Statement  

{Knight : Set K } {Knave : Set K}
{h : Knight ∩ Knave = ∅ }
(h' : ¬ (B ∈ Knave))
(h'' : ∀ (x: K), x ∈ Knight ∨ x ∈ Knave)
  :  B ∈ Knight := by
{
-- simp
  have BKK := h'' B
  cases BKK
  assumption
  contradiction
  -- use this exercise to introduce disjucntive syllogism and say that this reasoning is true in general(if needed by future levels).

  -- introduce ¬¬ p → p
  -- first approach by contradiction
  /-
  by_contra h''
  have h' := eq_false h'
  have h'' := eq_false h''
  rw [h',h''] at h1
  simp at h1
  -/

  -- second approach, direct
  --have h' := eq_false h'
  --rw [h'] at h1
  --simp at h1
  --assumption

}

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
