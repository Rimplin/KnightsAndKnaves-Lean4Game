import Game.Metadata
import Game.Doc.doc

World "EquationalReasoning" 
Level 1

Title "`rfl`, A Number Equals Itself" 

Introduction "In this exercise, we will prove `2 = 2`

`rfl` will do the job.

`rfl` is short for reflexivity, which is the property that for any number `a`, `a = a`

"

Statement 
  : 2 = 2 := by

  {
    rfl 
  }





Conclusion "Notice that 'level completed! 🎉' on the bottom. We say that the goal is closed/proven. "

/- Use these commands to add items to the game's inventory. -/

NewTactic rfl
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

