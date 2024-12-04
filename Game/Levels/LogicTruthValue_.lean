--import Game.Levels.LogicTruthValue_.L01_Propositions
--import Game.Levels.LogicTruthValue_.L02_Intro
import Game.Levels.LogicTruthValue_.L03_Intro
--import Game.Levels.LogicTruthValue_.L04_And
import Game.Levels.LogicTruthValue_.L05_And
--import Game.Levels.LogicTruthValue_.L06_Or
import Game.Levels.LogicTruthValue_.L07_Or
--import Game.Levels.LogicTruthValue_.L08_Implication
import Game.Levels.LogicTruthValue_.L09_Implication
import Game.Levels.LogicTruthValue_.L05_ImpGoal

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
In this world, we will be dealing with `Objects` of type `Prop` i.e propositions. You can think of a proposition as a statement that is either true or false(obviously, it can't be both at the same time). You have seen propositions before like `x=2`, `y=6` etc..

When you have `h : P` where `P : Prop` , then we say `h` is a proof of the statement `P`(imagine `x=2` instead of `P` if you wish). 

In a proof state, this would look like the following:
```
Objects
P : Prop
Assumptions
h : P
```

Moreover, we will discuss constructing new propositions from old ones.

Here's an example in natural language, given the two propositions 'The sun is shining' , 'It is Monday', you can construct 'The sun is shining and it is monday'. 

Another example would be, having the following:
```
h : `x=2`
h' : `y=6`
```
where `P` is `x=2` and `Q` is `y=6`, we can construct a new proposition `P ∧ Q` which is read as `x=2 and y=6`. Here we know what `P`,`Q` stand for. But, the proposition `P ∧ Q` can still be constructed and reasoned about regardless. Think of reasoning about unknown numbers like `x`,`y` etc...
"

#check of_eq_true
#check of_eq_false
#check eq_true
#check eq_false
