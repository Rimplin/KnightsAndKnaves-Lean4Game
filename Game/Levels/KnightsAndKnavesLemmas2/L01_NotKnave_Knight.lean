import Game.Metadata



--Statement  
--
--{Knight : Set K } {Knave : Set K}
--{h : Knight ∩ Knave = ∅ }
--{h1 : Xor' (A ∈ Knight) (B ∈ Knave) }
--{h2: Xor' (B ∈ Knight)  (B ∈ Knave) }
--(h' : ¬ (B ∈ Knave))
--  :  A ∈ Knight := by
--{
--
--  -- explain precedence so users can understand the unfolded result.
--  unfold Xor' at h1
--
--  -- introduce ¬¬ p → p
--  -- first approach by contradiction
--  /-
--  by_contra h''
--  have h' := eq_false h'
--  have h'' := eq_false h''
--  rw [h',h''] at h1
--  simp at h1
--  -/
--
--  -- second approach, direct
--  have h' := eq_false h'
--  rw [h'] at h1
--  simp at h1
--  assumption
--
--}
#check notright_left

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

#check Set.inter_eq_right

/-
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
--DefinitionDoc Xor' as "Xor'" 
--NewDefinition Xor' 
