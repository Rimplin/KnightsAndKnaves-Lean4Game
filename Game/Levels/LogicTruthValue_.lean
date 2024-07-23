import Game.Levels.LogicTruthValue_.L01_Propositions
import Game.Levels.LogicTruthValue_.L02_Intro
import Game.Levels.LogicTruthValue_.L03_And
import Game.Levels.LogicTruthValue_.L04_Implication
--import Game.Levels.Logic.L03_Or
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
In this world, you will also learn how to construct new propositions by connecting other propositions with logical connectives. 

Just as a quick example: 
Let `P` be the proposition 'It is cloudy' and let `Q` be the proposition 'It is raining'. Out of these two atomic propositions, we can form the compound proposition 'It is cloud `and` it is rainy' denoted `P ∧ Q` where `∧` means `and` in the propositional world. 

# quick overview

## proving statements involving logicla connectives
Every logical connective has an introduction rule which introduces a new expression involving propositions with that connective.

## unpacking information from a complicated propositional statement
Logical connective has some 'elimination' or 'unpacking rule' which unpacks the information within that complication expression.

# shifting between the two perspectives

"
#check of_eq_true
#check of_eq_false
#check eq_true
#check eq_false
