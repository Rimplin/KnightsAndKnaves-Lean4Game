import Game.Metadata


World "Logic" 
Level 5

Title "asdf" 

Introduction 
"
Negation of a proposition `P`, denoted `¬P`, is defined as `P → False`. Notice that this is an implication which you have learned to deal with in the previous level. 
Before dealing with negation directly, we will explain `False` in this level.

# What is `False` exactly? 
## As a type
`False` is the type that has no inhabitants, i.e there is no object, say `h`, that is of type `False`. In other words, we cannot find an `h` such that `h :False`. This makes sense when considering the propositions as types interpretation. It's impossible to have `h:False` because this would mean we have a 'witness/proof' for falsity, i.e we proved something that is false to be true.
## How to prove `False`?
Well, when was the first time you saw `False`?
Here:
'
Negation of a proposition `P`, denoted `¬P`, is defined as `P → False`. 
'
It should be clear that to get to false, you would need to prove `¬P`, and `P`. Then given such a proof state:
```
hnP : ¬P
hP : P
```
we can obtain false by `hnP hP`.
Proving a proposition and its negation is whats called deriving a contradiction.

## Principle of explosion

Moreover, `False` has no introduction rule , so the reasoning describe above is the only way to obtain an object of type `False`. If it did, or if you were able to find `h:False` then our system is worthless because we can prove anything. Such a system would be called an inconsistent system because of a contradiction.
will be discussed in previous, but the basic idea is that if you have in your proof state and `h` such that `h:False` then you can prove any proposition you want. In other words, within this proof state, all propositions are true. This is obviously absurd because it would mean for every proposition `p`, `p` is true and also `¬p` is true.
"

variable {q : Prop}
Statement 
  : False → q := by

  {
    intro h 
    exact False.elim h
  }





Conclusion 
"asdf
"

/- Use these commands to add items to the game's inventory. -/

--NewTactic 
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

