import Game.Levels.Logic.L01_Intro
import Game.Levels.Logic.L02_And
import Game.Levels.Logic.L03_Or
import Game.Levels.Logic.L04_Implication

World "Logic"
Title "Logic"
Introduction "In this world, we will be dealing with `Objects` of type `Prop` i.e propositions. You can think of a proposition as a statement that is either true or false(obviously, it can't be both at the same time).

Moreover, these statements are denoted by a symbol like `P`,`Q`,`R`.

# examples of propositions
'The Lean theorem prover had a 4.70 release' is a true statement.
'World War 2 ended in 1950' is a false statement. It ended in 1945.

# Building New Propositions From Previous Ones
In this world, you will also learn how to construct new propositions by connecting other propositions with logical connectives

## Logical Connectives

### `And` , `∧`
Let `p` denote the proposition 'The official language of France is french'(which is true).
Let `q` denote the prposition 'The official language of Germany is german'(which is true as well).
Combining these two prpositions together gives us the proposition `p ∧ q` which translate to English: 'The official language of Franch is french `And` the official language of Germany is german'. Because the two propositions connected by the `And` are true, then the entire statement is true as well. It's not hard to see that `p` or `q` being false would make `p ∧ q` false

# truth table
```
| P | Q | P ∧ Q  |
|---|---|--------|
| T | T |   T    |
| T | F |   F    |
| F | T |   F    |
| F | F |   F    |
```

Image \"images/Logic/Truth-Table-And.png\"
"

