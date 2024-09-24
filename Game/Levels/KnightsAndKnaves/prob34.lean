import Game.Metadata



example
  --sets
  {Knight : Set Inhabitant} {Knave : Set Inhabitant}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{h2: B ∈ Knight ∨ B ∈ Knave }
{h3: C ∈ Knight ∨ C ∈ Knave }
{stA : A ∈ Knight  ↔ (B ∈ Knave) }
{stAn : A ∈ Knave ↔ ¬ (B ∈ Knave) }
{stB: B ∈ Knight ↔ (A ∈ Knight ∧ C ∈ Knight ∨ A ∈ Knave ∧ C ∈ Knave) }
{stBn: B ∈ Knave ↔ ¬ (A ∈ Knight ∧ C ∈ Knight ∨ A ∈ Knave ∧ C ∈ Knave) }
  : C ∈ Knave  := by

  {
   have AOr := h1
   rcases h1 with AKnight|AKnave
   · have BKnave := stA.mp AKnight
     have BCnotsametype := stBn.mp BKnave
     rw [not_or] at BCnotsametype
     rw [not_and_or] at BCnotsametype
     rw [not_and_or] at BCnotsametype
     have AC:= BCnotsametype.left
     rw [Knave_NotKnightIff h h3] 

     rw [Knight_NotKnaveIff h AOr] at AKnight
     rw [NotKnight_KnaveIff h AOr] at AC
     exact notleft_right AC AKnight
   · have BKnight := stAn.mp AKnave
     rw [NotKnave_KnightIff h h2] at BKnight  
     have AC := stB.mp BKnight
     cases AC
     · rw [Knave_NotKnightIff h AOr] at AKnave
       exfalso
       exact AKnave h_1.left
     · exact h_1.right
  }





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/



-- NewTactic rw rfl
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

