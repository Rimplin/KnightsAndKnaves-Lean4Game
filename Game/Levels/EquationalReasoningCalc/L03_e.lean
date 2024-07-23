import Game.Metadata

World "EquationalReasoningCalc" 
Level 3

Title "" 

Introduction 
"
This is new but similar to the previous level.
"

    /-

  calc
    u = u +  t/2 - t/2 := by ring
    _ = 3 - t/2 := by rw [h2]
    _ = 3 - 3/2 := by rw [h1]
    _ = 3/2 := by norm_num
    -/
/-

  calc
    r = r + 2 * s - 2 * s := by ring
    _ = -1 - 2 * s := by rw [h2]
    _ = -1 - 2 * 3 := by rw [h1]
    _ = -7 := by ring

-/

-- ring, h2 , h1 ,ring
Statement {t u : ℝ} (h1 : t = 2) (h2 : u + t/2 = 3) : u = 2 := by
{

  Template
    calc
      -- create a `u + t/2` to be able to get rid of `u`
      u = (u +  t/2) - t/2 := by sorry

      -- get rid of `u + t/2` getting rid of `u`
      _ = 3 - t/2 := by sorry

      -- get rid of `t`, only being left with numbers now
      _ = 3 - 2/2 := by sorry

      -- carry out the operations on the numbers
      _ = 2 := by sorry
}

Conclusion 
"

"

/- Use these commands to add items to the game's inventory. -/

--NewTactic 
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

