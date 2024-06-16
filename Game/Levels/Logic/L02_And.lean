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
Giving these two proofs to the And introduction rule will construct a proof of `P ∧ Q`.

Here's the type of `And.intro`:
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





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

NewTactic And.intro constructor
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

