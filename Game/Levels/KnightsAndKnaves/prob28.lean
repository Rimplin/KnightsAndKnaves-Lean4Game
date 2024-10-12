--import Game.Metadata
---- problem 28
--variable (Knight : Finset K) (Knave : Finset K)
--
--#check XorToOr
--example
--  {inst : DecidableEq K}
--{h : Knight ∩ Knave = ∅ }
--{h1 : A ∈ Knight ∨ A ∈ Knave }
--{h2: B ∈ Knight ∨ B ∈ Knave }
--{stA : A ∈ Knight  ↔ ((A ∈ Knave) ∨ (B ∈ Knave)) }
--  : A ∈ Knight ∧ B ∈ Knave := by
--  {
--  -- book way, can't be further optimized
--    have AnKnave: A ∉ Knave := by 
--      intro AKnave
--      have AOrB : A ∈ Knave ∨ B ∈ Knave := by left ; exact AKnave 
--      have AKnight := stA.mpr AOrB
--      exact disjoint h AKnight AKnave
--
--    have AKnight := notinright_inleft h1 AnKnave 
--    constructor
--    · assumption
--    · have AknOrB := stA.mp AKnight
--      exact notleft_right AknOrB AnKnave 
--  }
--

import Game.Metadata
open Set

variable {K : Type}

World "KnightsAndKnaves"
Level 4

Title "lev 2"

Introduction "In this problem, there are only two people, A and B, each of 
whom is either a knight or a knave. A makes the following 
statement: 'At least one of us is a knave.' 
What are A and B? "

open Lean Parser Elab Tactic
elab "show_goal" t:tactic : tactic => do
  logInfoAt t m!"⊢ {(← Elab.Tactic.getMainTarget)}"
  evalTactic t

def getTacs (t1 : Syntax) : Array Syntax :=
  match t1 with
    | .node _ ``tacticSeq #[.node _ ``tacticSeq1Indented #[.node _ `null args]] =>
      args.filter (! ·.isOfKind `null)
    | _ => #[t1]

elab "show_goals1 " tacs:tacticSeq : tactic => do
  let tacs := getTacs tacs
  for t in tacs do
    evalTactic (← `(tactic| show_goal $(⟨t⟩)))

elab "show_goals " tacs:tacticSeq : tactic => do
  let tacs := getTacs tacs
  let _ ← tacs.mapM fun t => do
    match t with
      | `(tactic| · $ts) => evalTactic (← `(tactic| · show_goals1 $(⟨ts.raw⟩)))
      | _ => evalTactic (← `(tactic| show_goals1 $(⟨t⟩)))


--(uni : Knight ∪ Knave) 
-- theres x and y, x says at least one of us is a knave
  -- diff formalization to stx
  --(stx : (A ∈ Knight) ↔ (A ∈ Knight ∧  B ∈ Knave)
   --                 ∨ (A ∈ Knave ∧ B ∈ Knight)
   --                 ∨ (A ∈ Knave ∧ B ∈ Knave)  )
Statement 
  {inst : DecidableEq K}
  (Knight : Finset K)
  (Knave : Finset K) 
  (h : Knight ∩ Knave = ∅ )
(all : ∀ (x : K), x = A ∨ x = B)
  (h'' : ∀ (x: K), x ∈ Knight ∨ x ∈ Knave)
  (stA : A ∈ Knight ↔ Knave.card ≥ 1)
  : A ∈ Knight ∧ B ∈ Knave:= by

  have AnKnave : A ∉ Knave := by 
    intro AKnave
    have AKnave2 := AKnave
    rw [inright_notinleftIff (h'' A) h]  at AKnave
    have le1 := (Function.mt stA.mpr) AKnave
    push_neg at le1
    rw [Nat.lt_one_iff] at le1
    rw [Finset.card_eq_zero] at le1
    rw [le1] at AKnave2
    contradiction
  rw [notinright_inleftIff (h'' A) h] at AnKnave 
  
  have atleast := stA.mp AnKnave
  have BnKnight : B ∉ Knight := by
    intro BKnight
    have Knaveemp := all2_in_one_other_empty h all AnKnave BKnight
    rw [Knaveemp] at atleast
    contradiction
  
  rw [notinleft_inrightIff (h'' B) h] at BnKnight
  exact And.intro AnKnave BnKnight

--Raymond Smullyan, what is the name of this book, problem 28
example 
  {inst : DecidableEq K}
  (Knight : Finset K ) (Knave : Finset K) 
  --(uni : Knight ∪ Knave) 
  (h : Knight ∩ Knave = ∅ )
  -- theres x and y, x says at least one of us is a knave
  --rules of the game, i.e knights tell the truth but knaves lie

  (h'' : ∀ (x: K), x ∈ Knight ∨ x ∈ Knave)
  (stx : (x ∈ Knight) ↔ (x ∈ Knight ∧  y ∈ Knave)
                    ∨ (x ∈ Knave ∧ y ∈ Knight)
                    ∨ (x ∈ Knave ∧ y ∈ Knave)  )
--goal
  : x ∈ Knight ∧ y ∈ Knave:= by
  {
  --show_goals
  cases ( h'' x)
  · cases h'' y
    · constructor
      assumption
      -- since goal is impossible to directly prove, we neeed a proof by contradiction
      have stx2 := stx
      rw [not_iff_not.symm] at stx
      have conc := stx2.mp h_1
      -- notice that the negation of the right hand side of stx2 is true
      have this := eq_true h_1
      have this2:= eq_true h_2
      
      --have this3 := inleft_notinright h_1
      simp[this,this2] at conc
      have this3:= inleft_notinright h h_1
      have this4:= eq_false this3
      simp[this4] at conc
      assumption

       
       
    · constructor
      assumption ; assumption
  · cases h'' y
    · have := not_iff_not.mpr stx
      have this2:= this.mp (inright_notinleft h h_1)
      contrapose this2
      simp
      right
      left
      constructor
      assumption;assumption
    · constructor
      · have := not_iff_not.mpr stx 
        have this2 := this.mp (inright_notinleft h h_1)
        contrapose this2
        simp
        right
        right
        constructor
        assumption ;assumption
      · assumption

  }
#check not_iff_not

---- old formalization, not organized
--Statement 
--  --sets
--  (Knight : Set K ) (Knave : Set K) 
--  --(uni : Knight ∪ Knave) 
--  (h : Knight ∩ Knave = ∅ )
--  (h1 : Xor' (x ∈ Knight) (x ∈ Knave) ) 
--  (h2: Xor' (y ∈ Knight)  (y ∈ Knave) )
--  -- theres x and y, x says at least one of us is a knave
--  --rules of the game, i.e knights tell the truth but knaves lie
--  (stx : x ∈ Knight → (x ∈ Knight ∧  y ∈ Knave)
--                    ∨ (x ∈ Knave ∧ y ∈ Knight)
--                    ∨ (x ∈ Knave ∧ y ∈ Knave)  )
--  (stnx : x ∈ Knave → ¬ ( (x ∈ Knight ∧  y ∈ Knave)
--                    ∨ (x ∈ Knave ∧ y ∈ Knight)
--                    ∨ (x ∈ Knave ∧ y ∈ Knave) ) )
----goal
--  : x ∈ Knight ∧ y ∈ Knave:= by
--  {
--
--   --rw [Xor'] at h1
--   --rw [Xor'] at h2
--   --exact h1
--   --rw [Eq.rfl h1 ( (x ∈ Knight ∧ x ∉ Knave)  ∨ (x ∈ Knave ∧ x ∉ Knight ) )] at h1
--   --cases h1
--   --cases h2
--
--   -- no need to take two cases, explain to the user why!!!!
--   cases h1 
--   --cases h2
--   
--   have contr :=  stx h_1.left 
--   rcases contr    
--
--   exact h_2
--
--   cases h_2 
--   have contr2 := mem_inter h_1.left h_3.left 
--   rw [h] at contr2
--   contradiction
--
--
--   have contr2 := mem_inter h_1.left h_3.left 
--   rw [h] at contr2
--   contradiction
--
--   have contr := stnx h_1.left
--   push_neg at contr
--   have yK := contr.right.left h_1.left 
--   have yk2 : y ∈ Knave := by {
--     rw [Xor'] at h2
--     cases h2 
--     have contr2:= h_2.left
--     contradiction
--
--     exact h_2.left
--   }
--  
--   have target := contr.right.right
--   have helpp := contrapositive target
--   push_neg at helpp
--   have done := helpp yk2
--   have := h_1.left
--   contradiction
--   --contrapose at target
--   --push_neg
--   --push_neg at target
--   --contrapose target
--   --push_neg at target
--  }
--
--
-- rewriting, making it neat
theorem organized 
  --sets
  (Knight : Set K ) (Knave : Set K)
  (h : Knight ∩ Knave = ∅ )
  (h1 : Xor' (x ∈ Knight) (x ∈ Knave) ) 
  (h2: Xor' (y ∈ Knight)  (y ∈ Knave) )
  -- theres x and y, x says at least one of us is a knave
  --rules of the game, i.e knights tell the truth but knaves lie
  (stx : x ∈ Knight → (x ∈ Knight ∧  y ∈ Knave)
                    ∨ (x ∈ Knave ∧ y ∈ Knight)
                    ∨ (x ∈ Knave ∧ y ∈ Knave)  )
  (stnx : x ∈ Knave → ¬ ( (x ∈ Knight ∧  y ∈ Knave)
                    ∨ (x ∈ Knave ∧ y ∈ Knight)
                    ∨ (x ∈ Knave ∧ y ∈ Knave) ) )
--goal
  : x ∈ Knight ∧ y ∈ Knave:= by
{ 
--show_goals
cases h1 with
| inl h_1 => 
  obtain ⟨xKnight, xnKnave⟩ := h_1 
  have xTruth := stx xKnight
  cases xTruth with 
  | inl h_1 => exact h_1
  | inr h_1 => cases h_1 with 
               | inl h_1 =>
               obtain ⟨xKnave,yKnight⟩ := h_1 
               contradiction

               | inr h_1 => 
               obtain ⟨xKnave,yKnave⟩ := h_1 
               contradiction
  
| inr h_1 => 
  obtain ⟨xKnave, xnKnight⟩ := h_1  
  have xLie := stnx xKnave
  push_neg at xLie
  obtain ⟨notneeded,ynKnight,ynKnave⟩:= xLie 
  have yNKnight := ynKnight xKnave
  have yNKnave := ynKnave xKnave
  cases h2 with 
    | inl h_1 => 
      obtain ⟨yKnight,_⟩:= h_1 
      contradiction
    | inr h_1 =>
      obtain ⟨yKnave,_⟩:= h_1 
      contradiction

}
-- no sorryAX
#print axioms organized

example : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
--  constructor -- ⊢ ¬(P ∨ Q) ↔ (¬P ∧ ¬Q)

  -- instead of relying on comment, have lean check it
  show ¬(P ∨ Q) ↔ (¬P ∧ ¬Q); constructor
  · intro h     -- ⊢ ¬(P ∨ Q) → ¬P ∧ ¬Q
    constructor       -- ⊢ ¬P ∧ ¬Q
    · intro hp        -- ⊢ ¬P
      exact h (Or.inl hp)
    · intro hq        -- ⊢ ¬Q
      exact h (Or.inr hq)  
  
  · intro h    -- ⊢ ¬P ∧ ¬Q → ¬(P ∨ Q)
    intro h1 -- ⊢ ¬(P ∨ Q) 
    cases h1 with -- ⊢ False
    | inl h_1 => exact h.left h_1 
    | inr h_1 => exact h.right h_1 


 


variable {P Q : Prop}
example : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  show_goals  -- <---  note the `show_goals` here!
  constructor
  · intro h
    constructor
    · intro hp
      exact h (Or.inl hp)
    · intro hq
      exact h (Or.inr hq)

  · intro h
    intro h1
    cases h1 with
    | inl h_1 => exact h.left h_1
    | inr h_1 => exact h.right h_1

example : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  show_goals
  constructor

  intro h
  constructor

  intro h1
  exact h (Or.inl h1)

  intro h1
  exact h (Or.inr h1)

  intro h
  intro h1
  cases h1
  exact h.left h_1
  exact h.right h_1

example : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  show_goals
  constructor
  · intro h
    constructor
    · intro h1
      exact h (Or.inl h1)
    · intro h1
      exact h (Or.inr h1)
  · intro h
    intro h1
    cases h1 with
    | inl h_1 => exact h.left h_1
    | inr h_1 => exact h.right h_1


example : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  show_goals
  constructor
  case mp =>
    intro h
    constructor
    case left =>
      intro h1
      exact h (Or.inl h1)
    case right =>
      intro h1
      exact h (Or.inr h1)
  case mpr =>
    intro h
    intro h1
    cases h1 with
    | inl h_1 => exact h.left h_1
    | inr h_1 => exact h.right h_1

example : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) where
  mp h := by
    constructor
    · intro p
      apply h
      exact .inl p
    · intro q
      apply h
      exact .inr q
  mpr h h' := by
    cases h' with
    | inl h' => exact h.1 h'
    | inr h' => exact h.2 h'


example : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) where
  mp h := by
    constructor
    · intro p
      apply h
      exact .inl p
    · intro q
      apply h
      exact .inr q
  mpr h h' := by
    cases h' with
    | inl h' => exact h.1 h'
    | inr h' => exact h.2 h'


example (h : p ∨ q) : q ∨ p := by
  show_goals
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq


Conclusion "."

/- Use these commands to add items to the game's inventory. -/


-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

NewTactic show_goals obtain
