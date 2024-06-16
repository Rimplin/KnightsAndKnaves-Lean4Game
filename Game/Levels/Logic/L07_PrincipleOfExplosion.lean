import Game.Metadata


World "Logic" 
Level 7

Title "Principle Of Explosion" 

Introduction 
"
Otherwise known as 'from contradiction, anything follows'. 
This principle asserts that if you have contradictory assumptions then you can prove anything.
Example of contradictory assumptions:
```
h: P
nh: ¬P
```

Why this principle is valid?
"
variable {P Q: Prop}
Statement (h : P) (nh : ¬P)
  : Q := by

  {
    contradiction
  }





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

NewTactic contradiction
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

