import Game.Metadata
-- file which contains knights and knaves problems we made up.


World ""
Level 

Title ""

Introduction 
"
A : All of us are knights
B: Exactly one of us is a knave
"

Statement
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{all2 : ∀ (x : Inhabitant), x = A ∨ x = B}
{Or : ∀(x :Inhabitant), x ∈ Knight ∨ x ∈ Knave}
{stA : A ∈ Knight ↔ (Knight={A,B}) }
{stAn : A ∈ Knave ↔ ¬ (Knight={A,B}) }
{stB: B ∈ Knight ↔  (Knave={A} ∨ Knave={B}) }
{stBn: B ∈ Knave ↔  ¬ (Knave={A} ∨ Knave={B}) }
  : A∈ Knave := by

  {
    rcases Or B with BKnight|BKnave
    · have oneknave := stB.mp BKnight 
      rcases oneknave with KA|KB
      · exact mem_of_eq_singleton KA
      · #check mem_of_eq_singleton  
        have BKnave := mem_of_eq_singleton KB
        exfalso
        exact disjoint h BKnight BKnave
    · by_contra AKnight 
      rw [notinright_inleftIff (Or A) h] at AKnight
      have KAB := stA.mp AKnight 
      #check Finset.eq_of_not_mem_of_mem_insert
      #check Finset.erase_eq_iff_eq_insert
      #check Finset.insert_eq 
      -- Knight = {A,B} ∧ all ↔ A ∈ Knight ∧ B ∈ Knight 
      -- Knight = {A,B} → A ∈ Knight ∧ B ∈ Knight

      have : Knight={A,B} → B ∈ Knight := by 
        intro h'
        rw [h']
        exact mem2_iff_or_finset.mpr (all2 B)

      #check Finset.insert_eq_of_mem 
      have BKnight := this KAB
      exact disjoint h BKnight BKnave
  }

Conclusion 
"
"
