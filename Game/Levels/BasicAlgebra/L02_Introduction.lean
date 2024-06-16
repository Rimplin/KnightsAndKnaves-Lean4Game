import Game.Metadata


World "BasicAlgebra" 
Level 2

Title "Introd" 

Introduction "
In this level, we have `Objects`, `Assumptions`, and the `Goal`.

# Objects
For this world, objects will always be unknown numbers, or variables we are working with. Anything after the `:` denotes the type of whats before the `:`. 

Here, `x`  denotes a number but we don't know which number it is. The `:ℕ` in `x : ℕ` means that `x` is a variable of type natural number(positive numbers like `1`,`2`,`3`, and so on...). 

# Assumptions
As for the assumptions, we have `h: x=2` which means that `h` is an object of type `x=2`. This essentially means that `h` is an object asserting that the statement `x=2` is true or in other words, is a proof of `x=2`.

# Goal
Our goal is to prove that `x = 2`. To do this, we should let Lean know that we have a term that 'exactly' matches that goal. Notice that we do, that term is `h`!

Using `exact h` will do."

variable (x : ℕ )
Statement (h : x=2)
  : x=2 := by

  {
    exact h
  }





Conclusion ""

/- Use these commands to add items to the game's inventory. -/

NewTactic exact
-- NewLemma Nat.add_comm Nat.add_assoc

DefinitionDoc Nat as "ℕ"  
NewDefinition Nat 

