import Game.Metadata



example
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave :Finset Inhabitant}
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
     rw [inright_notinleftIff h3 h] 

     rw [inleft_notinrightIff AOr h] at AKnight
     rw [notinleft_inrightIff AOr h] at AC
     exact notleft_right AC AKnight
   · have BKnight := stAn.mp AKnave
     rw [notinright_inleftIff h2 h] at BKnight  
     have AC := stB.mp BKnight
     cases AC
     · rw [inright_notinleftIff AOr h] at AKnave
       exfalso
       exact AKnave h_1.left
     · exact h_1.right
  }





Conclusion 
"
"

