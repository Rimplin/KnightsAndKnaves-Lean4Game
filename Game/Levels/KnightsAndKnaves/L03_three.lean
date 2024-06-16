import Game.Metadata


World "KnightsAndKnaves"
Level 3

Title ""

Introduction 
"
"

Statement
  --sets
  (Knight : Set K ) (Knave : Set K)
(h : Knight ∩ Knave = ∅ )
(h1 : Xor' (x ∈ Knight) (x ∈ Knave) ) 
(h2: Xor' (y ∈ Knight)  (y ∈ Knave) )
  --rules of the game, i.e knights tell the truth but knaves lie
  (stx : x ∈ Knight → y ∈ Knight) (sty: y ∈ Knight → (x ∈ Knight ∧ y ∈ Knave) ∨ (x ∈ Knave ∧ y ∈ Knight) )
  (stxn : x ∈ Knave →  y ∈ Knave) (styn: y ∈ Knave → ¬ ( (x ∈ Knight ∧ y ∈ Knave) ∨ (x ∈ Knave ∧ y ∈ Knight) ) )
--goal
  :  := by

  {

  }





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/



-- NewTactic rw rfl
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

