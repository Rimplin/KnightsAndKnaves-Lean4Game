import Game.Metadata


World "LogicTruthValue_" 
Level 12 
--
--Title "" 
--
--Introduction 
--"
--"

Statement 
  :∀ (h:x), x  := by

  {
  intro h
  exact h
  }





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

--NewTactic 
-- NewTheorem Nat.add_comm Nat.add_assoc
/--
if the goal looks like:
```
∀ x, ...
```
then intro <nameOfVariable> will take an arbitrary x. 
-/
DefinitionDoc forallquantifier as "∀"
NewDefinition forallquantifier
