import Game.Levels.LogicTruthValue_.L01_Propositions
import Game.Levels.LogicTruthValue_.L02_Intro
import Game.Levels.LogicTruthValue_.L03_Intro
import Game.Levels.LogicTruthValue_.L04_And
import Game.Levels.LogicTruthValue_.L05_And
import Game.Levels.LogicTruthValue_.L06_Or
import Game.Levels.LogicTruthValue_.L07_Or
import Game.Levels.LogicTruthValue_.L08_Implication
import Game.Levels.LogicTruthValue_.L09_Implication
import Game.Levels.LogicTruthValue_.L10_False
import Game.Levels.LogicTruthValue_.L11_Not
import Game.Levels.LogicTruthValue_.L12_False
import Game.Levels.LogicTruthValue_.forall
--import Game.Levels.LogicTruthValue_.L03_And
--import Game.Levels.LogicTruthValue_.L04_Implication
--import Game.Levels.LogicTruthValue_.L05_BuildTruthTable
--import Game.Levels.Logic.L03_Or
--import Game.Levels.Logic.L05_False
--import Game.Levels.Logic.L06_Not
--import Game.Levels.Logic.L07_contrapositive
--import Game.Levels.Logic.L08_PrincipleOfExplosion
--
--Image "images/Logic/Truth-Table-And.png"
World "LogicTruthValue_"
Title "Logic Truth Value_"
Introduction 
"
This world will heavily rely on the truth table perspective of propositions and the various logical connective to provide an intuitive foundation for explaining the validity of various rules in propositional logic. 'Propositions' will be explained here, and the rest will be hinted at here but fully explained throught the levels.

In this world, we will be dealing with `Objects` of type `Prop` i.e propositions. You can think of a proposition as a statement that is either true or false(obviously, it can't be both at the same time).

Moreover, these statements are denoted by a symbol like `P`,`Q`,`R`.
For example, the proposition 'World War 2 ended in 1950' is false. It ended in 1945. After denoting this statement with `Q`, we can say that `Q` is `False`

# Building New Propositions From Previous Ones
In this world, you will also learn how to construct new propositions by connecting other propositions with logical connectives. 

Just as a quick example: 
Let `P` be the proposition 'It is cloudy' and let `Q` be the proposition 'It is raining'. Out of these two atomic propositions, we can form the compound proposition 'It is cloudy `and` it is rainy' denoted `P ∧ Q` where `∧` in the propostional world means `and`. This is translation from english to propositional notation, we will not be concerned directly with the details of this process but will use it to intuitively convey how propositional logic works.

## Connecting Propositions With A Logical Connective
It is important to note that connecting two proposition via a logic connective results in a proposition as well. If this wasn't the case, then how could we talk about the truth value of `P ∧ Q` if `P ∧ Q` were not a proposition! This proposition constructed using a logical connective and other propositions, like any other proposition, has a truth value. This truth value depends on the truth value of the propositions it was built out of and the rules of the logical connective. This is clearly illustrated in a truth table. 
Here's an example:

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
