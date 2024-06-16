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
variable {P Q : Prop}
/-- asdfasdfd asdfsadfdsa here -/
TheoremDoc modus_ponens as "modus_ponens" in "logic"
Statement modus_ponens (p : P) (ptoq: P → Q)
  : Q := by

  {
    exact ptoq p
  }





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

--TheoremDoc mul_left_cancel as "mul_left_cancel" in "*"
--NewTheorem mul_left_cancel 

/- asdf -/
--TheoremDoc modus_ponens as "modus_ponens" in "logic"
--NewTheorem modus_ponens 

/- some info -/
--TheoremDoc mul_left_cancel as "mul_left_cancel" in "*"
--NewTheorem mul_left_cancel 
-- NewDefinition Nat Add Eq
NewTheorem
