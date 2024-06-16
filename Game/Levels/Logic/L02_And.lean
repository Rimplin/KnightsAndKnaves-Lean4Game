import Game.Metadata

variable (P Q R : Prop)

World "Logic" 
Level 2

Title "And" 

Introduction 
"In this level, we will learn about the `∧` logical connective, known as 'And'.
In logic, for `P,Q` propositions, `P and Q` is true when both `P` is true and `Q` is true.
So in Lean, to prove `P ∧ Q`, you need a proof of `P` and a proof of `Q`.
Giving these two proofs to the And introduction rule will construct a proof of `P ∧ Q`.

Here's the type of `And.intro`:
```
  And.intro  (left : P) (right : Q) : P ∧ Q
```
where `P Q : Prop`


"

Statement (hP : P) (hQ : Q)
  : P ∧ Q  := by

  {
    Hint (hidden:=true) "Try `exact And.intro hP hQ`" 
    exact And.intro hP hQ 
  }





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

NewTactic And.intro
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

