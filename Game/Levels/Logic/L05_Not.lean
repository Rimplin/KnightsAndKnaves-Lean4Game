import Game.Metadata


World "Logic" 
Level 5

Title "Not, ¬" 

Introduction 
"
```
| P |  ¬P    |
|---|--------|
| T |   F    |
| F |   T    |
```

"

Statement 
  : 2=2  := by

  {
    rfl
  }





Conclusion ""

/- Use these commands to add items to the game's inventory. -/

/-
Testing rfl description1
-/
--TacticDoc rfl
--NewTactic rw rfl
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
NewDefinition
