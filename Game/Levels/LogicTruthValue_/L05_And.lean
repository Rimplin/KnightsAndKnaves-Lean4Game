import Game.Metadata


World "LogicTruthValue_" 
Level 2

Title "And" 

Introduction 
"
# Building New Propositions From Previous Ones
In this world, you will also learn how to construct new propositions by connecting other propositions with logical connectives. 
The logical connective presented here is `∧` read as 'and'.

Remember the example given at the beginning of the world. We restate it here:
Given the two propositions `x=2`, `4*y=16` , we can construct a new propositon `x=2 ∧ 4*y=16` which is read as `x=2 and 4*y=16`.
Instead of `x=2` , think `P`. instead of `4*y=16` think `Q`. (or the other way around)
Denoting `x=2` by `P` and `4*y=16` by `Q`, we can construct a new proposition `P ∧ Q` which is read as `x=2 and 4*y=16`. 

What is the truth value of this new proposition `x=2 ∧ 4*y=16`? 
Well, it would depend on truth value of the two component propositions `x=2` ,`4*y=16`. 

What possibilities are there for each's truth value? `x=2` can either be true or false and similarly for `4*y=16`. Here is a truth table that goes through all these possibilities: 
`T` stands for true
`F` stands for false
```
| x=2 | 4*y=16 | x=2 ∧ 4*y=16  |
|---|---|--------|
| T | T |   T    |
| T | F |   F    |
| F | T |   F    |
| F | F |   F    |
```

The proposition `x=2 ∧ 4*y=16` is true when `x=2` is true AND `4*y=16` is true.
In other words, if `P` is true AND `Q` is true. This is how things work regarless of what `P` is, what `Q` is.
Therefore, the more general truth table is the same:
```
| P | Q | P ∧ Q  |
|---|---|--------|
| T | T |   T    |
| T | F |   F    |
| F | T |   F    |
| F | F |   F    |
```

In this level, we have a proof of `P`(i.e `P` is true), and a proof of `Q` (i.e `Q` is true). We want to construct a proof of `P ∧ Q`. 

The `And` introduction rule will enable us to prove statements involving `∧`:
```
  And.intro  (left : P) (right : Q) : P ∧ Q
```
An example using it would be : 
```
And.intro left right
```
`And.intro` takes a proof of `P`, a proof of `Q`, and transforms/evaulates them to a proof of `P ∧ Q` where `P Q : Prop`.

"
-- Notice that `And.intro hP hQ` has type `P ∧ Q` which is EXACTLY the goal. Let Lean know.

-- In logic, for `P,Q` propositions, `P and Q` is true when both `P` is true and `Q` is true, being false otherwise.

/-
## Connecting Propositions With A Logical Connective
It is important to note that connecting two proposition via a logic connective results in a proposition as well. If this wasn't the case, then how could we talk about the truth value of `P ∧ Q` if `P ∧ Q` were not a proposition! This proposition constructed using a logical connective and other propositions, like any other proposition, has a truth value. This truth value depends on the truth value of the propositions it was built out of and the rules of the logical connective. This is clearly illustrated in a truth table. 

## `constructor` tactic
Using the `constructor` tactic will split a goal of the form `P ∧ Q` into two subgoals `P`,`Q` where you can deal with each one separately

### Example: `And` , `∧`
And.left h
And.right h

The atomic propositions in the compound proposition `p ∧ q` are : `p`, `q`. Of course, `p ∧ q` can be used to construct more complicated propositions.
-/

Statement (P Q : Prop) (hP : P) (hQ : Q)  
  : P ∧ Q  := by
  {
    Hint (hidden:=true) "Try `exact And.intro hP hQ` or `constructor`" 
    Branch
       exact And.intro hP hQ 
    Hint 
    "
    The constructor tactic transformed the goal `P ∧ Q` into two subgoals the first being `P` and the second being `Q`. This way of doing things matches the meaning of the `∧` connective.
    "
    constructor
    Hint "Notice that the goal is now `P`"
    exact hP
    Hint "After closing the goal `P`, you now have to close the goal `Q`"
    exact hQ
  }

Conclusion 
"
"

NewTactic  constructor
NewTheorem And.intro 
