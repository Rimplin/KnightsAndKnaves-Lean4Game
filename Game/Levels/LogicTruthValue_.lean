import Game.Levels.LogicTruthValue_.L01_Propositions
--import Game.Levels.Logic.L01_Intro
--import Game.Levels.Logic.L02_And
--import Game.Levels.Logic.L03_Or
--import Game.Levels.Logic.L04_Implication
--import Game.Levels.Logic.L05_False
--import Game.Levels.Logic.L06_Not
--import Game.Levels.Logic.L07_contrapositive
--import Game.Levels.Logic.L08_PrincipleOfExplosion
--
--Image "images/Logic/Truth-Table-And.png"
World "LogicTruthValue_"
Title "Logic Truth Value_"
Introduction "
This world will heavily rely on the truth table perspective of propositions and the various logical connective to provide an intuitive foundation for explaining the validity of various rules in propositional logic. 'Propositions' will be explained here, and the rest will be hinted at here but fully explained throught the levels.

In this world, we will be dealing with `Objects` of type `Prop` i.e propositions. You can think of a proposition as a statement that is either true or false(obviously, it can't be both at the same time).

Moreover, these statements are denoted by a symbol like `P`,`Q`,`R`.

# Building New Propositions From Previous Ones
In this world, you will also learn how to construct new propositions by connecting other propositions with logical connectives

## Logical Connectives
It is important to note that connecting two proposition via a logic connective results in a proposition as well. This proposition, like any other proposition, has a truth value. This truth value depends on the truth value of the atomic propositions and the rules of the logical connective. This point will be reiterated and hopefully fully materialize in your head as you deal with various logical connectives and as we discuss truth tables(see below for an example).

Every logical connective has an introduction rule which introduces a new expression involving propositions with that connective and some 'elimination' or 'unpacking rule' which unpacks the information within such an expression.

### Example: `And` , `∧`
And.intro
And.left h
And.right h

As an example, we present the `∧` logical connective.
Let `p` denote the proposition 'The official language of France is french'(which is true).
Let `q` denote the prposition 'The official language of Germany is german'(which is true as well).
Combining these two prpositions together gives us the proposition `p ∧ q` which translated to English: 'The official language of France is french `And` the official language of Germany is german'. Because the two propositions connected by the `And` are true, then the entire statement is true as well. It's not hard to see that one of or both `p` or `q` being false would make `p ∧ q` false. In other words, `p ∧ q` is true when `p` is true and `q` is true. It is false otherwise.

The atomic propositions in the compound proposition `p ∧ q` are : `p`, `q`. Of course, `p ∧ q` can be used to construct more complicated propositions.

# truth table 
The truth table of a logical connective illustrates the rule for that logical connective , i.e the truth value of the compound statement depending on the truth value of the atomic propositions.
The following truth table illustrates this for the prevously discussed `∧` connective.

`T` stands for true
`F` stands for false
```
| P | Q | P ∧ Q  |
|---|---|--------|
| T | T |   T    |
| T | F |   F    |
| F | T |   F    |
| F | F |   F    |
```
"
