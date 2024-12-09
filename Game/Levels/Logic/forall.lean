import Game.Metadata

World "LogicTruthValue_" 
Level 12 
--
--Title "" 
--
--Introduction 
--"
--"

Statement (a : x=y)
  :∀ (h:x), y  := by

  {
  -- split_ifs
  --positivity
  subst a
  exact fun h => h
  }

Conclusion 
"
"

/--
if the goal looks like:
```
∀ x, ...
```
then intro <nameOfVariable> will take an arbitrary x. 
-/
DefinitionDoc forallquantifier as "∀"
NewDefinition forallquantifier
