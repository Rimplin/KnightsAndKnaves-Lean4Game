import Game.Metadata

example 
  --sets

  [inst : DecidableEq K]
  (A B C : K)
--  (AneB : A ≠ B)
--  (BneC : B ≠ C)
--  (AneC : A ≠ C)
  (Knight : Finset K ) (Knave : Finset K)
  {Normal : Finset K}
--{hK : Finset Knight}
--{hKn : Finset Knave}
--{hN : Finset Normal}
--{finKnight : Fintype Knight}
--{finKnave : Fintype Knave}
--{finNormal : Fintype Normal}
--{OneKnight : Finset.card ( Knight) =1 }
--{OneKnave : Finset.card Knave =1 }
--{OneNormal : Finset.card Normal =1 }

{hKKn : Knight ∩ Knave = ∅ }
{hKN : Knight ∩ Normal = ∅ }
{hKnN : Knave ∩ Normal = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave ∨ A ∈ Normal }
{h2 : B ∈ Knight ∨ B ∈ Knave ∨ B ∈ Normal }
{h3 : C ∈ Knight ∨ C ∈ Knave ∨ C ∈ Normal}
{stA : A ∈ Knight → (B ∈ Knight) } 
{stAn : A ∈ Knave → ¬ (B ∈ Knight) }
{stB : B ∈ Knight → (A ∉ Knight)}
{stBn : B ∈ Knave → ¬(A ∉ Knight)}
: 2=2 := by 
  sorry
