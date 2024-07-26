import Game.Metadata

variable (P Q R : Prop)

World "Logic" 
Level 2

Title "And" 

Introduction 
"
In this level, we will learn about the `∧` logical connective, known as 'And'.
In logic, for `P,Q` propositions, `P and Q` is true when both `P` is true and `Q` is true.


# Two ways of dealing with ∧ in the goal(Try both!)
In Lean, to prove `P ∧ Q`, you need a proof of `P` and a proof of `Q`.

## first way
Giving these two proofs to the And introduction rule will construct a proof of `P ∧ Q`. Here's the type of `And.intro`:
```
  And.intro  (left : P) (right : Q) : P ∧ Q
```
where `P Q : Prop`

## second way
Using the `constructor` tactic will split a goal of the form `P ∧ Q` into two subgoals `P`,`Q` where you can deal with eac one separetly

"

Statement (hP : P) (hQ : Q)
  : P ∧ Q  := by

  {
    Hint (hidden:=true) "Try `exact And.intro hP hQ` or `constructor`" 
    Branch
       exact And.intro hP hQ 
    constructor
    Hint "Notice that the goal is now `P`"
    exact hP
    Hint "After closing the goal `P`, you now have to close the goal `Q`"
    exact hQ
  }


-- try it 
--open Classical

-- distributivity
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      Or.elim (h.right)
        (fun hq : q =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
        (fun hr : r =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (fun hpq : p ∧ q =>
          have hp : p := hpq.left
          have hq : q := hpq.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩)
        (fun hpr : p ∧ r =>
          have hp : p := hpr.left
          have hr : r := hpr.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro 
  (fun h : p ∧ (q ∨ r) =>
    Or.elim (h.right) 
    (fun hq : q => Or.inl (And.intro h.left hq))
    (fun hr : r ↦ Or.inr (And.intro h.left hr))
  )

  (fun h ↦ 
   Or.elim h 
   (fun hpq ↦ And.intro (hpq.left) (Or.inl hpq.right))
   (fun hpr ↦ And.intro (hpr.left) (Or.inr hpr.right)) )

-- an example that requires classical reasoning
example (p q : Prop) : ¬(p ∧ ¬q) → (p → q) :=
  fun h : ¬(p ∧ ¬q) =>
  fun hp : p =>
  show q from
    Or.elim (Classical.em q)
      (fun hq : q => hq)
      (fun hnq : ¬q => absurd (And.intro hp hnq) h)









example (p q : Prop) : ¬(p ∧ ¬q) → (p → q) :=
  fun h => fun hp => Or.elim (Classical.em q) (fun hq ↦ hq) (fun nhq ↦ False.elim (h (And.intro hp nhq) ))
  

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := 
  Iff.intro 
  (fun hpq ↦ And.intro hpq.right hpq.left)
  (fun hqp ↦ And.intro hqp.right hqp.left)

example : p ∨ q ↔ q ∨ p := 
  Iff.intro
  (fun hpq ↦ Or.elim (hpq) (Or.inr) (Or.inl) )
  (fun hqp ↦ Or.elim (hqp) (Or.inr) (Or.inl))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := 
  Iff.intro 
  (fun hpqr ↦ 
  And.intro 
  hpqr.left.left 
  (And.intro hpqr.left.right hpqr.right)
  )
  (fun hpqr ↦ 
   And.intro 
   (And.intro hpqr.left hpqr.right.left)
   hpqr.right.right
   )

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := 
  Iff.intro 
  (
  fun hpqr ↦ Or.elim hpqr 
  (fun hpq ↦ 
   Or.elim hpq (Or.inl) (fun hq ↦ Or.intro_right p (Or.intro_left r hq))
  )
  (fun hr ↦ Or.intro_right p (Or.intro_right q hr) )
  )
-- p → (p ∨ q) ∨ r
  (fun hpqr ↦ 
  have this := @Or.inl p q 
  have this2 := @Or.inl (p∨q) (r)
  have this3 := Implies.trans this this2
  have this4 : q ∨ r → p ∨ (q ∨ r) := Or.inr

  Or.elim hpqr
  (Implies.trans this this2)
  (fun hqr ↦
  Or.elim hqr (fun hq ↦ Or.inl (Or.inr hq)) (fun hr ↦ Or.inr hr)
  )

  --(fun hpq ↦ Or.inl (Or.inl hpq) )
--   (Trans.trans (@Or.inl p q) (@Or.inl (p∨q) (r) )) 

  /-
  ( fun hp ↦ 
  Or.inl (Or.inl hp)  
  ) 
-/

)
  
-- distributivity
#check Or.inl
#check proof_irrel

-- done
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := 
  Iff.intro 
  (fun hpqr ↦ Or.elim hpqr 
     (fun hp ↦ And.intro (Or.inl hp) (Or.inl hp)) (fun hqr ↦ And.intro (Or.inr hqr.left) (Or.inr hqr.right)))

  (
  fun hpqpr ↦ 
    Or.elim (hpqpr.left) (Or.inl) 
    (fun hq ↦ 
    (Or.elim hpqpr.right (fun hp ↦ Or.inl hp) (fun hr ↦ Or.inr (And.intro hq hr) ))
    )

    )

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := 
  Iff.intro 
  (
  fun hpqr ↦ 
    fun hpq ↦ 
      (hpqr hpq.left) hpq.right
  )

  (fun hpqr ↦ fun hp ↦ fun hq ↦ hpqr (And.intro hp hq) )
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := 
 Iff.intro 
 (fun hpqr ↦ 
    And.intro 
    (fun hp ↦ hpqr (Or.inl hp) )
    (fun hq ↦ hpqr (Or.inr hq) )
 )

 (fun hprqr ↦ fun hpq ↦ Or.elim hpq (hprqr.left) (hprqr.right))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := 
  Iff.intro 
  (fun hnpq ↦ And.intro (fun hp ↦ hnpq (Or.inl hp) ) (fun hq ↦ hnpq (Or.inr hq) )
  )
  (fun hnpnq ↦ fun hpq ↦ Or.elim hpq (hnpnq.left) (hnpnq.right) )

example : ¬p ∨ ¬q → ¬(p ∧ q) := 
  fun hpq ↦ fun hnpq ↦ Or.elim hpq (fun hnp ↦hnp hnpq.left) (fun hnq ↦ hnq hnpq.right)

example : ¬(p ∧ ¬p) := fun hpnp ↦ hpnp.right hpnp.left
example : p ∧ ¬q → ¬(p → q) := 
  fun hpnq ↦ 
    fun hpq ↦ 
      hpnq.right (hpq hpnq.left)

example : ¬p → (p → q) :=
  fun hnp ↦ fun hp ↦ absurd hp hnp
example : ¬p → (p → q) :=
  fun hnp ↦ fun hp ↦ False.elim (hnp hp)

example : (¬p ∨ q) → (p → q) := 
  fun hnpq ↦ 
    fun hp ↦ 
      Or.elim hnpq (fun hnp ↦ absurd hp hnp) (fun hq ↦ hq)
example : p ∨ False ↔ p :=  
  Iff.intro 
  (fun h ↦ Or.elim h (fun hp ↦ hp) (fun hfalse ↦ False.elim hfalse))
  (fun hp ↦ Or.inl hp)
example : p ∧ False ↔ False := 
  Iff.intro 
  (fun hpf ↦ hpf.right)
  (fun hfalse ↦ False.elim hfalse)
example : (p → q) → (¬q → ¬p) := 
  fun hpq ↦ 
    fun hnq ↦ 
      fun hp ↦ 
        hnq (hpq hp)
Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

NewTactic And.intro constructor
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

