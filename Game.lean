import Game.Levels.BasicAlgebra
import Game.Levels.Logic
import Game.Levels.SetTheoryLemmas
import Game.Levels.KnightsAndKnaves
-- Here's what we'll put on the title screen
Title "Hello World Game111!!"
Introduction
"
This is a gamification of mathematical proofs. Every level has a `Goal`, which is what you are trying to prove. Closing the `Goal` means you have proved theorem and there is nothing else to do.

You will use the Lean theorem prover, and its mathematical library mathlib.

# Right Side Pane
Let's explain what's going on in the right side pane.

Anything you click on will display an overview and some examples. Refer back to it whenever you need to.

## Tactics
In this puzzle game, you will use tactics to manipulate the `Goal` and close it, essentially proving the `Goal`. Tactics will be incrementally introduced, and tactics that haven't been introduced yet will have a lock icon which means you can't use them yet. 
## Definitions
The point of this game is not just to showcase lean, but also to learn some mathematics. Relevant definitions will be displayed here

## Theorems
Here is listed theorems to use throughout the levels. Some you would have proved in previous levels and others are presented for you to use but without proof.

# Level Structure
Within every level, the `Objects`, `Assumptions`, and `Goal` for the current level will be display with a text input to execute tactics accordingly. Click on the main node in the `Basic Algebra` world to see what that looks like!
"

Info "
Here you can put additional information about the game. It is accessible
from the starting through the drop-down menu.

For example: Game version, Credits, Link to Github and Zulip, etc.

Many technical details have been skipped for the sake of not getting bogged down with Lean, but focus on the aspects of reasoning and proof. You can visit https://leanprover-community.github.io/mathlib4_docs/ for more information about any tactic used by searching `Mathlib.Tactic.tacticname`, and theorems.

Zulip chat for lean has been a very useful resource to resolve issues when formalizing the exercises, you can visit it and ask questions in the '#new members' stream. You can also view messages without signing up
"

/-! Information to be displayed on the servers landing page. -/
Languages "English"
CaptionShort "Game Template"
CaptionLong "You should use this game as a template for your own game and add your own levels."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"
Dependency BasicAlgebra → Logic → SetTheoryLemmas → KnightsAndKnaves
/-! Build the game. Show's warnings if it found a problem with your game. -/

MakeGame
