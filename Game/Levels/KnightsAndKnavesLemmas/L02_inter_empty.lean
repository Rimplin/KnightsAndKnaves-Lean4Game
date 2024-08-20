import Game.Metadata
import Game.Levels.KnightsAndKnavesLemmas.L01_NotKnave_Knight

World "KnightsAndKnavesLemmas"
Level 2

Title ""

Introduction 
"
"

-- knight_knave (h : x ∈ Knight) (h' : x ∈ Knave) : False , maybe extend contradiction to detect this...
Statement
  --sets
  (Knight : Set K ) (Knave : Set K)
(h : Knight ∩ Knave = ∅ )
(h1 : Xor' (A ∈ Knight) (B ∈ Knave) ) 
(h2: Xor' (B ∈ Knight)  (B ∈ Knave) )
(h' : A ∈ Knight) (h'' : A ∈ Knave)
--(stA : A ∈ Knight → () ) 
--(stAn : A ∈ Knave → ¬ () ) 
--(stB: B ∈ Knight → () )
--(stBn: B ∈ Knave → ¬ () )
  : False := by

  {
-- have := notKnave_Knight
   -- need the right version have := notKnave_Knight h'' 
   sorry
  }





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/



-- NewTactic rw rfl
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
