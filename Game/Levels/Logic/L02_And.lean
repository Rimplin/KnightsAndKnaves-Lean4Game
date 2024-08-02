import Game.Metadata

variable (P Q R : Prop)

World "Logic" 
Level 2

Title "And" 

Introduction 
"
In this level, we will learn about the `∧` logical connective, known as 'And'.
In logic, for `P,Q` propositions, `P and Q` is true when both `P` is true and `Q` is true, being false otherwise.


# Two ways of dealing with ∧ in the goal(Try both!)
In Lean, to prove `P ∧ Q`, you need a proof of `P` and a proof of `Q`.
## `And` introduction rule
In Lean, to prove `P ∧ Q`, you need a proof of `P` and a proof of `Q`. Using the `And` introduction rule, we can introduce `∧` in a newly constructed expression. 
The `And` introduction rule will enable us to prove statements involving `∧`.
For example, given the following proof state:
```
hP : P
hQ : Q
⊢ P ∧ Q
```
We can close the goal by:
```
exact And.intro hP hQ
```

Here's the type of `And.intro`:
```
  And.intro  (left : P) (right : Q) : P ∧ Q
```
`And.intro` takes a proof of `P`, a proof of `Q`, and transforms/evaulates to a proof of `P ∧ Q`
where `P Q : Prop`
### Example: `And` , `∧`
And.intro
And.left h
And.right h

The atomic propositions in the compound proposition `p ∧ q` are : `p`, `q`. Of course, `p ∧ q` can be used to construct more complicated propositions.
Giving these two proofs to the And introduction rule will construct a proof of `P ∧ Q`.


## `constructor` tactic
Using the `constructor` tactic will split a goal of the form `P ∧ Q` into two subgoals `P`,`Q` where you can deal with each one separately

# truth table 
Refer to the documentation in the right side pane.

"

variable {p : BooleanAlgebra Prop}
#check p.himp_eq P Q
Statement (hP : P) (hQ : Q) (hPQ: P ∧ Q)
  : P ∧ Q  := by

  {
    
--    tauto 
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
The constructor tactic transformed the goal `P ∧ Q` into two subgoals the first being `P` and the second being `Q`. This way of doing things matches the meaning of the `∧` connective.
"

/- Use these commands to add items to the game's inventory. -/

NewTactic  constructor
NewTheorem And.intro 
-- NewDefinition Nat Add Eq

