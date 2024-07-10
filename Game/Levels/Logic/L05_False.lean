import Game.Metadata


World "Logic" 
Level 5

Title "asdf" 

Introduction 
"
Negation of a proposition `P`, denoted `¬P`, is defined as `P → False`. Notice that this is an implication which you have learned to deal with in the previous level. 
For now, just know that `False` is a type that has no introduction rule and that proving `False` means deriving a contradiction. So, to prove `¬p` , you must assume `p` and derive a contradiction.

you cannot find an `h` such that `h:False`. 
Before dealing with negation directly, we will explain `False` in this level.

To emphasize the fact that negation is an implication, you have to go through this simple level.

`False` is the empty proposition, thus it has no introduction rule. It represents a contradiction.
What is a contradiction? Well, it is a propostional statement that is false for all possible values of its variables.
Example:

But in this context, we will use the term contradiction to refer the assertion or proof of a propositional statement that is false for all possible values of its variables.

# What is `False` exactly? 
## As a type
`False : Prop` is the type that has no inhabitants, i.e there is no object, say `h`, that is of type `False`. In other words, we cannot find an `h` such that `h :False`. This makes sense when considering that finding an `h:False` would mean we have proved something that is false. 

## How to prove `False` and what are the consequences?
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
Proving a proposition and its negation is whats called deriving a contradiction. A logical system that has this quality is called an inconsistent system.

## Principle of explosion
Moreover, `False` has no introduction rule , so the reasoning described above is the only way to obtain an object of type `False`. If you were able to find `h:False` i.e prove `False` then our system is worthless because we can prove anything. To reiterate, such a system would be called an inconsistent system because of a contradiction.

-- rules of inference like modus ponens need to be emphasized to make this understsanble. Also we can make the user prove the principle of explosion using modus ponens.
will be discussed in previous, but the basic idea is that if you have in your proof state an `h` such that `h:False` then you can prove any proposition you want. In other words, within this proof state, all propositions are true. This is obviously absurd because it would mean for every proposition `p`, `p` is true and also `¬p` is true.
"

variable {q : Prop}
Statement (h:p) (h':¬p)
  :  False := by

  {
    exact h' h
  }

/-

    have : p ∨ q := Or.inl h
    have this2 := disjunctiveSyllogism this h'
    assumption
-/



Conclusion 
"asdf
"

/- Use these commands to add items to the game's inventory. -/

--NewTactic 
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

