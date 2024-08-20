import Game.Metadata


World "LogicTruthValue_" 
Level 9

Title "Implication, →" 
#check Function.mt
#check Function.mtr
Introduction 
"
Logical implication `P → Q` is made up of two components:
- The premise, which in this case is `P`
- The conclusion, which in this case is `Q`

What logical implication does is that it takes evidence or proof for `P` and transforms it returning a proof of `Q`.
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
/- asdfasdfd asdfsadfdsa here -/
--TheoremDoc modus_ponens as "modus_ponens" in "logic"
Statement modus_ponens (p : P) (ptoq: P → Q)
  : Q := by


  { exact ptoq p }



Conclusion 
"
This is what is called an inference rule. It has two assumptions, `p : P` , `ptoq : P → Q` and the conclusion `Q`. It is an inference rule because we 'infer' a certain conclusion from assumptions or already established theorems.
Usually presented in this format:

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
--NewTheorem
/-- no lean docstring avaialble -/
DefinitionDoc imp as "→"
NewDefinition imp 
