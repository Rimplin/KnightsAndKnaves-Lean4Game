import Game.Metadata
import Game.Doc.doc


World "Logic" 
Level 3

Title "Or" 

Introduction 
"
In this level, you will learn about the `Or` logical connective.

# truth table
```
| P | Q | P ∨ Q  |
|---|---|--------|
| T | T |   T    |
| T | F |   T    |
| F | T |   T    |
| F | F |   F    |
```

From the truth table, we can see that if one of `P`,`Q` is true then `P ∨ Q` is true. 
Therefore, if we have `P ∨ Q` as our goal, it is enough to prove `P` or to prove `Q`.
This is exactly what the `left` and `right` tactic does. 
The `left` tactic transforms our goal from `P ∨ Q` to `P` and similarily for the `right` tactic. This is because Lean understands that if `P` is true, then `P ∨ Q` is true.
"
variable (P Q : Prop)

Statement (p : P) (q: Q)
  : P ∨ Q := by

  {
    Hint "Use either `left` or `right`"

    Branch
      left
      Hint "`p` is exactly the goal"
      exact p
    right
    Hint "`q` is exactly the goal"
    exact q
  }





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

NewTactic left right
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

