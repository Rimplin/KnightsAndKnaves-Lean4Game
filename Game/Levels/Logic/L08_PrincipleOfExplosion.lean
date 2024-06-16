import Game.Metadata


World "Logic" 
Level 8

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

Why is this principle is valid? Well, this is what you will hav e to prove in this level. For your convenience, the contradiction tactic will be unlocked so you don't have to do the same steps when there are contradictory assumptions.
"
variable {P Q: Prop}
Statement (h : P) (nh : ¬P)
  : Q := by

  {
    have helper : P ∨ Q := Or.inl h
  }


example (P : Prop) : ¬ (¬ P) ↔ P := by
  constructor
  · intro h
    push_neg at h
    assumption

  · intro h
    push_neg
    assumption


Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

NewTactic contradiction
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

