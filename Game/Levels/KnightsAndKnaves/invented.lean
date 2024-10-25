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



--A : All of us are knights
--B: Exactly one of us is a knave
theorem Ais_knave 

{inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{all2 : ∀ (x : Inhabitant), x = A ∨ x = B}
{Or : ∀(x :Inhabitant), x ∈ Knight ∨ x ∈ Knave}
{stA : A ∈ Knight ↔ (A ∈ Knave ∨ B ∈ Knave) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∨ B ∈ Knave) }
{AneB : A ≠ B}

: A ∉ Knight :=by 
  -- assume A Knight, so everyone is a knight, so B is a knight, so exactly one person is a knave, contradiction
  intro h1
  have := (stA).mp (h1 )

-- two cases B Knave, B Knight. B Knave done. do B Knight
  have h2 : B ∈ Knave:=by
  
    sorry
   -- have h3 : A ≠ B := by 
   -- {
   --   intro h4
   --   rw [h4] at h
   --   have h5 : A ∈ Knight ∩ Knave := by 
   --   {
   --     rw [(all2 A).resolve_left A] at h
   --     rw [←(Or A)] at h
   --     exact Or.intro_right  h
   --   }
      --rw [h] at h5
      --exact absurd h5 (h xS)
    
    --exact (stA B).mp $ by {
    --  by_contradiction h6,
    --  rw eq_empty_iff_forall_not_mem at h6,
    --  rcases h6 Knight with ⟨h7, h8⟩,
    --  exact h8.elim (h8.symm ▸ ((dec_trivial : A = A ≠ B).symm ▸ h1)),
    -- }
 -- 
 -- have h3 : A ≠ B := by {
 --   intro h4
 --   suffices : Knight = {B},
 --   {
 --     have h5 := stA A,
 --     rw h4 at h5,
 --     apply h5.mp (or.inl rfl),
 --   },
 --   suffices : Knight = {A, B},
 --   {
 --     rw this,
 --     apply or.inr rfl,
 --   },
 --   exact (stB B).mp h2,
 -- },
--  exact absurd ((stAn).mpr h1) $ (stAn).mpr ((stA).mp h2) h3
  sorry


-- A says I am a knave or B is a knave
example {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{all2 : ∀ (x : Inhabitant), x = A ∨ x = B}
{Or : ∀(x :Inhabitant), x ∈ Knight ∨ x ∈ Knave}
{stA : A ∈ Knight ↔ (A ∈ Knave ∨ B ∈ Knave) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∨ B ∈ Knave) }
 : A ∈ Knight ∧ B ∈ Knave := by
  have h1 : A ∈ Knight ∨ A ∈ Knave := (Or A)
  have h2 : B ∈ Knight ∨ B ∈ Knave := (Or B)
  cases h1
  -- A Knight
  · have h4 : A ∈ Knave ∨ B ∈ Knave := ((stA).mp h_1)
    cases h2 
    
    · -- absurd
      sorry  -- A Knight, B Knight, Bknave, contradiction
    · exact ⟨h_1,h_2⟩  
      -- h7 h8
      --cases h2 
      --
      --·  sorry
      --  -- absurd , Aknight A knave
     ----   exact absurd h4 $ (stAn A).mpr (or.inl h5)
      --
      --
      --· exact ⟨h7, h8⟩
      
    
  
  -- A Knave
  · 
    have h4  := (stAn ).mp h_1
    cases h2 
    {
      -- A ∈ Knave, A ∉ Knave, absurd to get contradiction
      sorry
      --exact absurd hA $ (stAn A).mpr (or.inr h7)
    }
    {
      -- do it
      sorry
      --exact ⟨h4, h7⟩
    }
  
