import Game.Metadata


inductive Solution (Knight : Finset Inhabitant) (Knave : Finset Inhabitant)
| submit (h : A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) : Solution (Knight) (Knave)
-- i could obfuscate this by making a type that when given the correct argument solves the exercise.
example
  --sets
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
  {all : ∀(x : Inhabitant), x = A ∨ x = B ∨ x = C}
  { AneB : A ≠ B}
  { BneC : B ≠ C}
  { AneC : A ≠ C}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{h2: B ∈ Knight ∨ B ∈ Knave }
{h3: C ∈ Knight ∨ C ∈ Knave }
{stA : A ∈ Knight  ↔ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave) }
{stB: B ∈ Knight ↔ (Knight = {A} ∨ Knight = {B} ∨ Knight = {C}) }
{stBn: B ∈ Knave ↔ ¬ (Knight = {A} ∨ Knight = {B} ∨ Knight = {C}) }
  : Solution Knight Knave:= by

  {
    -- this is similar to i am a knave
    have AKnave : A ∈ Knave := by 
      by_contra AKnight
      rw [notinright_inleftIff h1 h] at AKnight
      have AKnave := stA.mp AKnight
      exact disjoint h AKnight AKnave.left 

    have BKnight : B ∈ Knight := by {
      by_contra BKnave
      rw [notinleft_inrightIff h2 h] at BKnave

      --push_neg at stBn 
      --rw [not_and_or] at stAn
      --rw [not_and_or] at stAn
      -- 
      --simp[AKnave] at stAn 
      --simp[BKnave] at stAn 
       
      --have := stBn.mp BKnave
      have CKnight : C ∈ Knight := by 
        have Knaves := stAn.mp AKnave
        repeat rw [not_and_or] at Knaves
        --push_neg at Knaves
        simp [AKnave,BKnave] at Knaves
        exact notright_left h3 Knaves 

       
      have KnighteqC : Knight = {C} := by
        #check Set.eq_of_subset_of_subset   
        rw [Finset.eq_singleton_iff_unique_mem] 
        constructor
        · assumption
        -- make a theorem of this and for all the cases
        · intro x
          intro xK
          cases all x
          · rw [h_1] at xK
            exfalso 
            exact disjoint h xK AKnave
          · cases h_1
            · rw [h_2] at xK
              exfalso
              exact disjoint h xK BKnave
            · assumption
      ---
      have BKnight:= stB.mpr (by right; right; assumption)
      exact disjoint h BKnight BKnave  
    }
    have CKnave : C ∈ Knave := by {
      have OneKnight := stB.mp BKnight
      by_contra CKnight 
      #check notright_left
      have CKnight := notright_left h3 CKnight
      cases OneKnight 
      · rw [h_1] at BKnight
        have := Finset.mem_singleton.mp BKnight
        symm at this
        contradiction
      · cases h_1 
        · rw [h_2] at CKnight
          have := Finset.mem_singleton.mp CKnight
          symm at this
          contradiction
        · rw [h_2] at BKnight
          have := Finset.mem_singleton.mp BKnight
          -- make a full version but for this, i can turn Knight={C} into card one and use full
          #check full
          contradiction
    }
    -- now submit
    sorry
      --contrapose this
      --rw [not_and_or]
      --rw [not_and_or]
      --right
      --right
      --push_neg
      --have KSub : Knight ⊆ {A,B,C} := by sorry
      --rw [inright_notinleftIff h1 h] at AKnave
      --rw [Finset.subset_insert_iff_of_not_mem AKnave] at KSub
      --rw [inright_notinleftIff h2 h] at BKnave
      --rw [Finset.subset_insert_iff_of_not_mem BKnave] at KSub
      --#check Finset.subset_singleton_iff
      --rw[ Finset.subset_singleton_iff] at KSub
      --have nonemp : Knight ≠ ∅ := sorry
      --cases KSub
      --contradiction
      --assumption
      -- have done this before, start from knight subset of A,B,C then remove... then state its non empty then do it...

    --have CKnave : C ∈ Knave := by 
    --  by_contra CKnight
    --  #check Set.mem_singleton_iff
    --  #check Set.eq_singleton_iff_unique_mem
    --  have Ors := stB.mp BKnight
    --  cases Ors
    --  · rw [Finset.eq_singleton_iff_unique_mem] at h_1 
    --    rw [inright_notinleftIff h1 h] at AKnave
    --    exact AKnave h_1.left
    --  · cases h_1 
    --    · rw [notinright_inleftIff h3 h] at CKnight
    --      rw [h_2] at CKnight
    --      rw [Finset.mem_singleton] at CKnight
    --      have : C ≠ B := sorry
    --      contradiction
    --    · rw [h_2] at BKnight
    --      rw [Finset.mem_singleton] at BKnight
    --      have : B ≠ C := sorry
    --      contradiction
    --exact Solution.submit (And.intro AKnave ( (And.intro BKnight CKnave)))

  }

example (S : Set K) (h : S ⊆ {A,B,C}) (h': A ∉ S) : S ⊆ {B,C} := by   
  sorry
   
#check Set.subset_insert_iff_of_not_mem




Conclusion 
"
"

