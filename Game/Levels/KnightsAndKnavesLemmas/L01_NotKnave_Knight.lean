import Game.Metadata



World "KnightsAndKnavesLemmas"
Level 1

Title ""

Introduction 
"
Before starting the riddles, some new concepts have to be clarified.
Xor...
it is obvious that no one can be a knight and a knave at the same time. If some is not a knave then they are a knight.
"

/-
Expect lesser hints and more freedom in this world, there are many solutions and tactics you can use to solve any given logic puzzle. and there are some variations to similar patterns of reasoning that can be successfully utilized.

In this game, you can be either a knight or a knave and certainly not both at the same time. This is expressed by the fact `h`, and is reinforced in this level
-/

--variable 
/-- 
asdf
-/

-- notKnave_Knight (h : ¬ (x ∈ Knave) ) : x ∈ Knight
TheoremDoc notKnave_Knight as "notKnave_Knight" in "Logic"
Statement notKnave_Knight 

{Knight : Set K } {Knave : Set K}
{h : Knight ∩ Knave = ∅ }
{h1 : Xor' (A ∈ Knight) (B ∈ Knave) }
{h2: Xor' (B ∈ Knight)  (B ∈ Knave) }
(h' : ¬ (B ∈ Knave))
  :  A ∈ Knight := by
{

  -- explain precedence so users can understand the unfolded result.
  unfold Xor' at h1

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
  have h' := eq_false h'
  rw [h'] at h1
  simp at h1
  assumption

}





Conclusion 
"
"

theorem memleft_empty_inter (A:Set K) (B: Set K)
(h: x ∈ A) (l: A ∩ B = ∅)
  : x ∉ B := by
  {
    intro h2
    have contr:= Set.mem_inter h h2
    rw [l] at contr 
    norm_num at contr
  --  contradiction
  }
/- Use these commands to add items to the game's inventory. -/



-- NewTactic rw rfl
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

--TheoremDoc Xor' as "Xor" in "logic"
--NewTheorem Xor' 



/-
since this is a repeated pattern in this world, we introduce it as its own level. You need to show that having two sets being disjoint (i.e sharing no common element) and having a common element is a contradiction. This is not an obvious contradiction( like p , ¬p) for the `contradiction` tactic to work. Some work needs to be done to get to that point.
Note the theorem:
```
Set.not_mem_empty.{u} {α : Type u} (x : α) : x ∉ ∅
```
An object of this type is given to you as an assumption in this level for your convenience and this you can also directly use this theorem.  can be used freely later on.

Hint: the goal is to get something that contradicts not_mem_empty. Since x belong to Knight and Knave then it belongs to their intersection which is equal to the empty set contradiction not_mem_empty. Let's do this step by step. (Make it feel like the player discovered this:
Notice that the only information we can derive is that x is in the intersection. Do we have information about the intersection? Well yes. its empty set so x ∈ empty set. Execute the finishing blow. 

This is a common theme when using `contradiction`, sometimes contradiction can't see the 'contradiction' and manipulating the proof state would reveal this to `contradiction`.
-/
theorem knight_knave 

/-
The reason for the assumption `h` is to ensure that no one can be a knight and a knave at the same time, being so would lead to a contradiction.

The reason for the assumption `h1` is to state that `A` is of type `K` and that it belongs to either the set `Knight` or `Knave` which are both sets of elements of type `K`. The sets `Knight` and `Knave` do not necessarily contain all elements of type `K`, which is why we need to be precise here.
-/
(Knight : Set K ) (Knave : Set K)
(h : Knight ∩ Knave = ∅ )
(h1 : Xor' (A ∈ Knight) (A ∈ Knave) ) 
(h2: Xor' (B ∈ Knight)  (B ∈ Knave) )
(h' : A ∈ Knight) (h'' : A ∈ Knave) : False := by 
   have := Set.mem_inter h' h''
   rw [h] at this
   have this2 : ∀ x:K, x ∉ ∅  := Set.not_mem_empty 
   contradiction



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
-- simplifying the conditions, also the Xor' conditions won't be necessary after the notKnave_Knave (etc ...) stuff
example (Knight : Set K ) (Knave : Set K) (A : K)
(h : Knight ∩ Knave = ∅ ) : Xor' (A ∈ Knight) (A ∈ Knave) ↔ A ∈ Knight ∨ A ∈ Knave := by 
  constructor
  unfold Xor' at *
  · intro h'
    cases h'
    · exact Or.inl (h_1.left)
    · exact Or.inr (h_1.left)
  · intro h'
    unfold Xor'
    cases h'
    · left
      constructor
      assumption
      -- this is just KnightNotKnave, introduce those two first then this... nice!
      by_contra
      have := Set.mem_inter h_1 a
      rw [h] at this
      contradiction
    · right
      constructor
      assumption
      by_contra
      have := Set.mem_inter a h_1
      rw [h] at this
      contradiction

#check Set.inter_eq_right
/--
def Xor' (a b : Prop) := (a ∧ ¬ b) ∨ (b ∧ ¬ a)

# Exclusive Or 

## Rewriting Xor'
`Xor' p q` can be rewritten as:
```
(p ∧ ¬q) ∨ (¬p ∧ q)
```
To rewrite `Xor'` in the goal:
```
rw [Xor']
```

To rewrite `Xor'` in hypothesis `h`:
```
rw [Xor'] at h
```
-/
DefinitionDoc Xor' as "Xor'" 
NewDefinition Xor' 
NewTheorem notKnave_Knight
