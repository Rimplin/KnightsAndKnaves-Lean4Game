import Game.Metadata
import Game.Doc.doc

World "EquationalReasoning" 
Level 1

Title "A Number Equals Itself" 

Introduction "In this exercise, we will prove `2 = 2`

`rfl` will do the job.

`rfl` is short for reflexivity, which is the property that for any number `a`, `a = a`

`rfl` also applies more generally, `rfl` will close any goal of the form `A=B` where `A`,`B` are identical. If needed, `rfl` will unfold both sides into their definitions and then check if they are equal. In other words, `rfl` can prove the equality of two things that are 'equal by definition'.
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

