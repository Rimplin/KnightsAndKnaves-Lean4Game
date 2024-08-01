import Game.Levels.LogicTruthValue_.L01_Propositions
import Game.Levels.LogicTruthValue_.L02_Intro
import Game.Levels.LogicTruthValue_.L03_And
import Game.Levels.LogicTruthValue_.L04_Implication
import Game.Levels.LogicTruthValue_.L05_BuildTruthTable
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
Add documentation from here into type Prop to avoid repetition in `Logic` world.

This world will heavily rely on the truth table perspective of propositions and the various logical connective to provide an intuitive foundation for explaining the validity of various rules in propositional logic. 'Propositions' will be explained here, and the rest will be hinted at here but fully explained throught the levels.

In this world, we will be dealing with `Objects` of type `Prop` i.e propositions. You can think of a proposition as a statement that is either true or false(obviously, it can't be both at the same time).

Moreover, these statements are denoted by a symbol like `P`,`Q`,`R`.
For example, the proposition 'World War 2 ended in 1950' is false. It ended in 1945. After denoting this statement with `Q`, we can say that `Q` is `False`

# Building New Propositions From Previous Ones
In this world, you will also learn how to construct new propositions by connecting other propositions with logical connectives. 

Just as a quick example: 
Let `P` be the proposition 'It is cloudy' and let `Q` be the proposition 'It is raining'. Out of these two atomic propositions, we can form the compound proposition 'It is cloudy `and` it is rainy' denoted `P ∧ Q` where `∧` in the propostional world means `and`. This is translation from english to propositional notation, we will not be concerned directly with the details of this process but will use it to intuitively convey how propositional logic works.

# quick overview

## proving statements involving logical connectives
This will involve using inference rules that are intuitively true from the truth table perspective. 

## unpacking information from a complicated propositional statement
N/A

# shifting between the two perspectives
"

#check of_eq_true
#check of_eq_false
#check eq_true
#check eq_false
