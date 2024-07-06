import Game.Metadata


World "Logic" 
Level 5

Title "asdf" 

Introduction 
"
Negation of a proposition `P`, denoted `¬P` is defined as `P → False`. 
Before dealing with negation directly, we will explain `False` in this level.

# What is `False` exactly? 
## As a type
`False` has no introduction rule.
`False` is the type that has no inhabitants, i.e there is no object, say `h`, that is of type `False`. In other words, we cannot find an `h` such that `h :False`. This makes sense when considering the propositions as types interpretation. It's impossible to have `h:False` because this would mean we have a 'witness' for falsity, i.e we proved something that is false to be true.
## Principle of explosion
will be discussed in previous, but the basic idea is that if you have in your proof state and `h` such that `h:False` then you can prove any proposition you want. In other words, within this proof state, all propositions are true. This is obviously absurd because it would mean for every proposition `p`, `p` is true and also `¬p` is true.
"

Statement 
  :  := by

  {

  }





Conclusion 
"asdf
"

/- Use these commands to add items to the game's inventory. -/

--NewTactic 
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

