import Game.Metadata


#check propext
World "LogicTruthValue" 
Level 

Title "" 

Introduction 
"
\\begin{array}{|c c|c|} 
\\hline
P & Q & P → Q \\\\
\\hline
T & T & T \\\\
T & F & F \\\\
F & T & T \\\\
F & F & T \\\\
\\hline
\\end{array}
"

Statement (h: P ↔ Q)
  : P=Q := by

  {
  -- axioms and computations, theorem proving in lean 4
    exact propext h
  }





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

--NewTactic 
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

