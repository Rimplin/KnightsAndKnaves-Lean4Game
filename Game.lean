import Game.Levels.EquationalReasoning
import Game.Levels.EquationalReasoningAutomation
import Game.Levels.EquationalReasoningCalc
import Game.Levels.LogicTruthValue_
--import Game.Levels.Logic
import Game.Levels.LogicAlternative
import Game.Levels.SetTheoryLemmas
import Game.Levels.KnightsAndKnaves
import Game.Levels.KnightsAndKnaves2
-- Here's what we'll put on the title screen
Title "Reasoning"
Introduction
"
This is a gamification of mathematical proofs. Every level has a `Goal`, which is what you are trying to prove. Closing the `Goal` means you have proved the theorem and there is nothing else to do.

You will use the Lean theorem prover, and its mathematical library mathlib.

# Right Side Pane
Let's explain what's going on in the right side pane.

Anything you click on will display an overview and some examples. This will be available to you at all times when working on the levels. Refer back to it whenever you need to.

## Tactics
In this puzzle game, you will use tactics to manipulate the `Goal` and close it, essentially proving the `Goal`. Tactics will be incrementally introduced, and tactics that haven't been introduced yet will have a lock icon which means you can't use them yet. 

## Definitions
The point of this game is not just to showcase ***Lean***, but also to learn some mathematics. Relevant definitions will be displayed here

## Theorems
Here is listed theorems to use throughout the levels. Some you would have proved in previous levels and others are presented for you to use but without proof.

# Level Structure
Within every level, the `Objects`, `Assumptions`, and `Goal` for the current level. This is called the initial proof state. There will also be a text input to execute tactics accordingly.
***Lean*** tracks the proof state as you execute tactics. 
You will execute tactics one by one until Lean tells you that have closed the goal.

# More info
You can click the hamburger menu in the top right then 'Game Info' for more information.

# Terminlogy
"

Info "
Here you can put additional information about the game. It is accessible
from the starting through the drop-down menu.

For example: Game version, Credits, Link to Github and Zulip, etc.

Many technical details have been skipped for the sake of not getting bogged down with Lean and its mathematical library mathlib, but focus on the aspects of reasoning and proof. You can visit https://leanprover-community.github.io/mathlib4_docs/ for more information about any tactic used by searching `Mathlib.Tactic.tacticname`, and theorems.

Zulip chat for lean has been a very useful resource to resolve issues when formalizing the exercises, you can visit it and ask questions in the '#new members' stream. You can also view messages without signing up. There are other streams dedicated to various topics you can check out as well. 

# Editor Mode 
## copy and paste your solutions somewhere else
Some levels will force you to use editor mode. Editor mode is necessary for multiline tactics. Moreover, you should get used to it because it mimics a vscode Lean environment which is the most common way Lean is run.

To access editor mode, click on the icon to the left of the hamburger menu in the top right.
You can copy and paste your solutions if you have Lean setup, or you can use the lean web editor: https://live.lean-lang.org/ if you want to experiment with your solutions outside the lean game.
Make sure to have `import Mathlib.Tactic` at the top and then to copy whats above the editor area which is the problem statement. Each problem statement is of the form `example ... :=  by` and after that is where your solution should go.

## vscode like environment
Hovering over things will give you useful information.
# Links 
https://leanprover-community.github.io/
https://lean-lang.org/
https://lean-lang.org/documentation/

https://github.com/leanprover-community/mathlib4

https://leanprover.zulipchat.com/
https://zulip.com/case-studies/lean/

# how to navigate documentation
You can use https://leanprover-community.github.io/mathlib4_docs/ for Lean and mathlib related documentation. You can see 'Lean', 'Mathlib' in the left side pane, clicking on either will expand them. A more effective way of finding what you want is using the search feature of this page , using 'Go To Definition' if you have vscode setup for Lean and mathlib, or hovering over things to get more information

# Rules
You can relax the rules.

This is not recommended for people who have never heard about Lean before. Moreover, relaxing the rules would ruin the coherence and structured/guided experience you would have when playing the game normally. If that is what you are looking for, then don't relax the rules.

"

/-! Information to be displayed on the servers landing page. -/
Languages "English"
CaptionShort "Game Template"
CaptionLong "You should use this game as a template for your own game and add your own levels."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"
Dependency EquationalReasoning → LogicTruthValue_ → LogicAlternative → SetTheoryLemmas → KnightsAndKnaves
Dependency EquationalReasoning → EquationalReasoningAutomation
Dependency EquationalReasoning → EquationalReasoningCalc
/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
