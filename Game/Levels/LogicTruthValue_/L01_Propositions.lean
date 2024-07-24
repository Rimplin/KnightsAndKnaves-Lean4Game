import Game.Metadata


World "LogicTruthValue_" 
Level 1

Title "" 

Introduction 
"

# examples of propositions
You have seen propositions in 'Equational Reasoning'. Things like `x = 2`, `y = 6` are propositions i.e of type `Prop`.
'The Lean theorem prover had a 4.70 release' is a true statement. After denoting this statement with `P`, we can say that `P` is `True` or `P = True`.

'World War 2 ended in 1950' is a false statement. It ended in 1945. After denoting this statement with `Q`, we can say that `Q` is `False` or `Q = False`.

These are called atomic propositions. Atomic propositions are ones which contain no logical connectives (like the previously discussed `∧`). You will also learn how to make compound propositions from atomic propositions using logical connectives.

# talk about editor mode and sorry, this is good because it would introduce them early on... in a world that every user is required to go through as part of the main experience.
# experiment using editor mode
Editor mode is a vscode like environment. The main thing we want to emphasize this level is that you can hover over things to get more information.
Use `#check` and hover your mouse to see what iit says.
Try:
```
#check 2=2
#check x=2
#check P=True 
...
```
`#check` gives the type of the expression that's after it.
Notice that `P=True` is of type Prop which means that it is an assertion that is either `True` or `False`. It is true i.e `(P=True)=True` when we find a proof `h : P = True`.
Whenever you are done, replace `sorry` with `rfl` to close the goal and move on.
"
variable {P : Prop}
/-- works here too? -/
Statement 
  : 2=2 := by

  {
  Template
    Hole
  rfl
  }





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

--NewTactic 
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

