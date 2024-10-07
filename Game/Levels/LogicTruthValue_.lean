--import Game.Levels.LogicTruthValue_.L01_Propositions
--import Game.Levels.LogicTruthValue_.L02_Intro
import Game.Levels.LogicTruthValue_.L03_Intro
--import Game.Levels.LogicTruthValue_.L04_And
import Game.Levels.LogicTruthValue_.L05_And
--import Game.Levels.LogicTruthValue_.L06_Or
import Game.Levels.LogicTruthValue_.L07_Or
--import Game.Levels.LogicTruthValue_.L08_Implication
import Game.Levels.LogicTruthValue_.L09_Implication
--import Game.Levels.LogicTruthValue_.L10_False
import Game.Levels.LogicTruthValue_.L11_Not
import Game.Levels.LogicTruthValue_.L12_False
--import Game.Levels.LogicTruthValue_.forall
--import Game.Levels.LogicTruthValue_.L03_And
--import Game.Levels.LogicTruthValue_.L04_Implication
--import Game.Levels.LogicTruthValue_.L05_BuildTruthTable
--import Game.Levels.Logic.L03_Or
--import Game.Levels.Logic.L05_False
--import Game.Levels.Logic.L06_Not
--import Game.Levels.Logic.L07_contrapositive
--import Game.Levels.Logic.L08_PrincipleOfExplosion
--Image "images/Logic/Truth-Table-And.png"
World "LogicTruthValue_"
Title "Logic Truth Value_"
Introduction 
"
-- these are the most important points that need to be focused on but switching to a truth value perspective disrupts this... truth value perspective should be introduced to show the brute force way of solving knights and knaves puzzles.
In this world, we will be dealing with `Objects` of type `Prop` i.e propositions. You can think of a proposition as a statement that is either true or false(obviously, it can't be both at the same time). You have seen propositions before like `x=2`, `4*y=16` etc..

We construct new propositions from old ones. For example, denoting `x=2` by `P` and `4*y=16` by `Q`, we can construct a new proposition `P ∧ Q` which is read as `x=2 and 4*y=16`. 

Having an object `h` of type `P` where `P` is of type `Prop` means that `h` is a proof of `P`. You have seen a special case of this for `x=2` for example, but this applies for any proposition.

-----------------------------
This world will heavily rely on the truth table perspective of propositions and the various logical connective to provide an intuitive foundation for explaining the validity of various rules in propositional logic. 'Propositions' will be explained here, and the rest will be hinted at here but fully explained throught the levels.

# quick overview

## proving statements involving logical connectives
This will involve using inference rules that are intuitively true from the truth table perspective. 

## unpacking information from a complicated propositional statement

# shifting between the two perspectives
"

#check of_eq_true
#check of_eq_false
#check eq_true
#check eq_false
