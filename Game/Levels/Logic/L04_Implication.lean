import Game.Metadata


World "Logic" 
Level 4

Title "Implication, →" 

Introduction 
"
Logical implication `P → Q` is made up of two components:
- The premise, which in this case is `P`
- The conclusion, which in this case is `Q`

# truth table
```
| P | Q | P → Q  |
|---|---|--------|
| T | T |   T    |
| T | F |   F    |
| F | T |   T    |
| F | F |   T    |
```

A statement `P → Q` is false when `P` is true and `Q` false, it's true otherwise.
"

Statement 
  :  := by

  {

  }





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

--NewTactic rw rfl
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

