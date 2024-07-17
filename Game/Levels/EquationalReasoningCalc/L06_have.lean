import Game.Metadata


World "EquationalReasoningCalc" 
Level 6

Title "" 

Introduction 
"
"

Statement 
  :  := by

  {

  }



-- fully have proof?? structured derivations
example {x : ℚ} (h : 3 * x + 6 = 16 - x) : x = 5/2 := by 
  -- one step solve or structure proof, tedious...
  --linarith [h]
  have h1 : 3 * x = 16 - x - 6 := by linarith [h]

  have h2 : 4*x = 10 := by linarith [h1]
  have h3 : x = 5/2 := by linarith [h2]
  exact h3
  

Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

--NewTactic 
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

