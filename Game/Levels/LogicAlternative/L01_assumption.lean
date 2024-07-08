import Game.Metadata


World "LogicAlternative" 
Level 1

Title "`assumption` tactic" 

Introduction 
"
Let's introduce the first 'automation' tactic. 
The point behind such tactics is that there are tedious patterns of reasoning and automation tactics alleviate the burden of having to spell them out into Lean every time. 

Automations will sacrifice ... for brevity which is less tedious but might be more obfuscated.

One pattern of reasoning you will almost always encounter is having an assumption of a type that 'exactly' matches the goal. The `exact` tactic suggests itself here, but you could just write `assumption`. The `assumption` tactic will use the assumptions in the proof state to prove the goal.

Try it out!
"

variable {P Q : Prop}
Statement (hP: P) (hQ: Q) (hR : R)
  : P := by
  {
    assumption
   --Hint (hidden := true) "Type `exact hP`!"
  }





Conclusion 
"
Informally, the `assumption` tactic looks through the assumptions in the proof state and tries to find one which has a type that matches the goal through the assumptions in the proof state and tries to find one that which has a type that matches the goal. In this case, that would be `hP` and the type would be `P`.

The `assumption` tactic is capable of alot more, but it will not be used in this game. You can read more about these capabilities in the right side pane documentation

The advantage of the `assumption` tactic over exact is that you don't have to spell out the assumption to Lean. However, it might be clearer to explicity do so. This is the tradeoff between brevity and ...
"

/- Use these commands to add items to the game's inventory. -/

NewTactic assumption
