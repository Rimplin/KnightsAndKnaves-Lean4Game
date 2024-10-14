--import Game.Metadata
---- break up every problem into multiple levels explaining the reasoning behind the solution
---- problem 26, what is the name of this book
---- notice that from the statement of B we can know that B is a knave, and then C correctly asserted that B is a knave so we get that C is a knight.(if someone tells the truth then they must be a knight because there is no other option, if there was someone that sometimes lies or tells the truth we can't know, therefore `iff` is more appropriate here and implication is more appropriate when such a character is present)
--
-- 
--
--
--#check imp_false
--/-
--English description of the below solution:
--
---/
--
--example
--  --sets
--  (Knight : Set K ) (Knave : Set K)
--(h : Knight ∩ Knave = ∅ )
--(h1 : Xor' (A ∈ Knight) (A ∈ Knave) ) 
--(h2: Xor' (B ∈ Knight)  (B ∈ Knave) )
--(h3: Xor' (C ∈ Knight)  (C ∈ Knave) )
---- instead of stB and stnB, we can use ↔ and the knowledge of negating both sides and all that
--(stB : B ∈ Knight → ( (A ∈ Knight → A ∈ Knave) ∧ (A ∈ Knave → A ∈ Knight) ))
--(stnB : B ∈ Knave → ¬( (A ∈ Knight → A ∈ Knave) ∧ (A ∈ Knave → A ∈ Knight) ))
--(stC : C ∈ Knight → B ∈ Knave)
---- should be ¬ (B ∈ Knave) instead of B ∈ Knight, but they are logically equivalent. prove that, need to examine and add levels for this.
--(stnC : C ∈ Knave → B ∈ Knight)
-- : B ∈ Knave ∧ C ∈ Knight := by{
--  rcases h3 with ⟨CKnight,CnKnave⟩|⟨CKnave,CnKnight⟩  
--
--  · -- C Knight
--    have := stC CKnight
--    constructor
--    assumption; assumption
--  · -- C Knave
--    -- here we want to prove that C is a knight but we know that C is not a knight, so we will have to derive some contradiction to get the goal we want
--    have := stnC CKnave
--    have ⟨KnightKnave,KnaveKnight⟩ := stB this
--    rcases h1 with ⟨AKnight,AnKnave⟩|⟨AKnave,AnKnight⟩  
--    · have := KnightKnave AKnight
--      contradiction
--    · have := KnaveKnight AKnave
--      contradiction
--  }
--
----example : A ∈ Knight ↔ A ∈ Knight ∧ B ∈ Knight := by 
----  simp 
----  #check imp_and
----  sorry
--
---- problem 26
---- new formalization
--#check XorToOr
--
--example
--  --sets
--  (Knight : Set K ) (Knave : Set K)
--(h : Knight ∩ Knave = ∅ )
--(h1 : A ∈ Knight ∨ A ∈ Knave ) 
--(h2: B ∈ Knight ∨ B ∈ Knave )
----(h3: C ∈ Knight ∨ C ∈ Knave )
---- instead of stB and stnB, we can use ↔ and the knowledge of negating both sides and all that
--(stB : B ∈ Knight ↔ ( A ∈ Knight ↔ A ∈ Knave  ) )
--(stC : C ∈ Knight ↔ B ∈ Knave)
-- : B ∈ Knave ∧ C ∈ Knight := by{
-- -- iff sometimes can be confusing , manipulate it
--  #check iff_iff_implies_and_implies
--  -- (p → q ∧ ¬p → ¬q)  ↔ (p ↔ q)
--  #check iff_iff_and_or_not_and_not
--  #check iff_and_self
--  #check iff_self_and
--  #check iff_iff_not_or_and_or_not
--  #check IffToIf
--  have :=IffToIf stB
--  have ⟨forward,backward⟩ := stB
--  --rw [iff_iff_implies_and_implies] at stB
--  --rw [not_iff_not.symm] at stB
--  --nth_rw 2 [not_iff_not.symm] at stB
--
--  cases h2
--  · rw [stB] at h_1
--    cases h1
--    · have := h_1.mp h_2
--      have this2:= Set.mem_inter h_2 this
--      rw [h] at this2
--      contradiction
--    · have := h_1.mpr h_2 
--      have this2:= Set.mem_inter this h_2
--      rw [h] at this2
--      contradiction
--  · constructor
--    assumption
--    rw [stC.symm] at h_1
--    assumption
--}
--
---- truth value simp approach, will solve any well formed puzzle... 
--example
--  --sets
--  (Knight : Set K ) (Knave : Set K)
--(h : Knight ∩ Knave = ∅ )
--(h1 : A ∈ Knight ∨ A ∈ Knave ) 
--(h2: B ∈ Knight ∨ B ∈ Knave )
--(h3: C ∈ Knight ∨ C ∈ Knave )
---- instead of stB and stnB, we can use ↔ and the knowledge of negating both sides and all that
--(stB : B ∈ Knight ↔ ( A ∈ Knight ↔ A ∈ Knave  ) )
--(stC : C ∈ Knight ↔ B ∈ Knave)
-- : B ∈ Knave ∧ C ∈ Knight := by{
--  have AOr:= h1
--  have BOr := h2
--  have COr := h3
--  cases h1
--  -- A Knight
--  · cases h2
--    -- B Knight
--    · cases h3
--      -- C Knight
--      · ---simp [eq_true h_1,h_1,h_2,h_3] at *
--        --rw [eq_true] at h_1
--        --simp [of_eq_true,eq_true,eq_true_intro] at *
--        --simp_rw [eq_true h_1] at *
--          
--        simp [eq_true h_1] at *
--        simp [eq_true h_2] at *
--        simp [eq_true h_3] at *
--        assumption   
--        --have h_1t := eq_true h_1 
--        --have h_2t := eq_true h_2 
--        --have h_3t := eq_true h_3 
--        --rw [Knight_NotKnaveIff h AOr] at h_1
--        --rw [Knight_NotKnaveIff h BOr] at h_2
--        --rw [Knight_NotKnaveIff h COr] at h_3
--        -- 
--        --have h_1f := eq_false h_1
--        --have h_2f := eq_false h_2
--        --have h_3f := eq_false h_3
--        --simp [h_1t,h_2t,h_3t,h_1f,h_2f,h_3f] at*
--          
--      -- C Knave
--      · 
--        have h_1t := eq_true h_1 
--        have h_2t := eq_true h_2 
--        have h_3t := eq_true h_3 
--        rw [Knight_NotKnaveIff h AOr] at h_1
--        rw [Knight_NotKnaveIff h BOr] at h_2
--        rw [Knave_NotKnightIff h COr] at h_3
--         
--        have h_1f := eq_false h_1
--        have h_2f := eq_false h_2
--        have h_3f := eq_false h_3
--        simp [h_1t,h_2t,h_3t,h_1f,h_2f,h_3f] at stB
--
--
--    -- B Knave
--    · cases h3  
--      · 
--        have h_1t := eq_true h_1 
--        have h_2t := eq_true h_2 
--        have h_3t := eq_true h_3 
--        rw [Knight_NotKnaveIff h AOr] at h_1
--        rw [Knave_NotKnightIff h BOr] at h_2
--        rw [Knight_NotKnaveIff h COr] at h_3
--         
--        have h_1f := eq_false h_1
--        have h_2f := eq_false h_2
--        have h_3f := eq_false h_3
--        have conj := And.intro stB stC
--        simp [h_1t,h_2t,h_3t,h_1f,h_2f,h_3f] at conj
--        -- just evaluates it to true which means the choice of A,B,C works
--        simp [h_2t,h_3t]
--         
--
--
--      · obtain h_1expr := eq_true h_1
--        have h_1t := eq_true h_1 
--        have h_2t := eq_true h_2 
--        have h_3t := eq_true h_3 
--        rw [Knight_NotKnaveIff h AOr] at h_1
--        rw [Knave_NotKnightIff h BOr] at h_2
--        rw [Knave_NotKnightIff h COr] at h_3
--         
--        have h_1f := eq_false h_1
--        have h_2f := eq_false h_2
--        have h_3f := eq_false h_3
--        simp [h_1t,h_2t,h_3t,h_1f,h_2f,h_3f] at*
--
--  -- A Knave
--  · cases h2
--    · cases h3
--      · --simp_rw [eq_true,eq_false,Knight_NotKnaveIff,Knave_NotKnightIff,NotKnave_KnightIff,NotKnight_KnaveIff] at *
--       --simp_rw  
--        sorry
--      · 
--        simp [eq_true h_1] at *
--        simp [eq_true h_2] at *
--        simp [eq_true h_3] at *
--        --assumption   
--        sorry
--    · cases h3  
--      · 
--        simp [eq_true h_1] at *
--        simp [eq_true h_2] at *
--        simp [eq_true h_3] at *
--        --assumption   
--      · 
--        simp [eq_true h_1] at *
--        simp [eq_true h_2] at *
--        simp [eq_true h_3] at *
--        assumption   
--}
--
--
--/-
--Knights and Knaves Logic Puzzle Using the Biconditional [Discrete Math Class] - YouTube
--https://www.youtube.com/watch?v=Imgus1ispQk
--
--Error - Invidious
--https://yewtu.be/watch?v=Ytddk4fDRSM
--
--Mathematical Visual Proofs - YouTube
--https://www.youtube.com/@MathVisualProofs/videos
--
--Discrete Mathematics - An Open Introduction
--https://discrete.openmathbooks.org/dmoi3.html
--
--Discrete Mathematics - dmoi3-tablet.pdf
--https://discrete.openmathbooks.org/pdfs/dmoi3-tablet.pdf
--
--Discrete Mathematics - An Open Introduction
--https://discrete.openmathbooks.org/dmoi3.html
--
--Propositional Logic
--https://discrete.openmathbooks.org/dmoi3/sec_propositional.html
--
--Discrete Mathematics
--https://discrete.openmathbooks.org/dmoi3/
--
--Knights, Knaves, and Propositional Logic [Discrete Math Class] - YouTube
--https://www.youtube.com/watch?v=C6PeX4iKJbU
--
--prolog knights and knaves - Invidious
--https://yewtu.be/search?q=prolog+knights+and+knaves
--
--Mnemeonics - Invidious
--https://yewtu.be/channel/UChK2sLYpeiB5qzAQwx0Id3g
--
--Error - Invidious
--https://yewtu.be/watch?v=oEAa2pQKqQU
--
--patrick massot interactive lean book at DuckDuckGo
--https://start.duckduckgo.com/lite/?q=patrick+massot+interactive+lean+book
--
--1. Introduction — Mathematics in Lean 0.1 documentation
--https://www.imo.universite-paris-saclay.fr/~patrick.massot/mil/01_Introduction.html
---/
--
---- AKnight ↔ stA ∧ BKnight ↔ stB
---- stB is not a proof, it would be just a shorthand to the proposition
--variable (A B C: K)
--variable   (Knight Knave: Set K ) 
--
--def stB := (A ∈ Knight ↔ A ∈ Knave)
--def stC := (B ∈ Knave)
--example 
--(h : Knight ∩ Knave = ∅ )
--(h1 : A ∈ Knight ∨ A ∈ Knave ) 
--(h2: B ∈ Knight ∨ B ∈ Knave )
--(h3: C ∈ Knight ∨ C ∈ Knave )
---- instead of stB and stnB, we can use ↔ and the knowledge of negating both sides and all that
-- : 
-- (
-- ( B ∈ Knight ↔ (stB A Knight Knave) ) 
-- ∧ 
-- (C ∈ Knight ↔ stC B Knave)
-- ) 
-- ↔ (B ∈ Knave ∧ C ∈ Knight) := by{
--   -- repharsing what the backward direction means : I know what B and C are , the conclusion would be that the ∧ of all the assumption is = True, meaning that this configuration and B and C do not contradict the assumptions and therefore are a possible answer.
--   #check stB
--   #check B ∈ Knight
--   constructor 
--   · intro h'
--     by_contra h''
--     --push_neg at h''
--     #check not_and_or
--     rw [not_and_or] at h''
--     cases h''
--     · rw [NotKnave_KnightIff h h2] at h_1
--       have Bconc := h'.left.mp h_1
--       unfold stB at Bconc
--       #check not_iff_self
--       rw [Knight_NotKnaveIff h h1] at Bconc
--       exact not_iff_self Bconc
--        
--     · #check stB
--       #check stC
--       sorry
--   · sorry
--   
-- }
--#check eq_true_intro
--#check eq_true


import Game.Metadata
World "KnightsAndKnaves" 
Level 2

Title "" 

Introduction 
"
Three of the inhabitants A, B, and C were standing together in a garden. 
A stranger passed by and asked A, 'Are you a knight or a knave?' A answered, but rather indistinctly, so the stranger could not make out what he said. The stranger than asked B, 'What did A say?' B replied, 'A said that he is a knave.' At this point the third man, C, said, 'Don't believe B; he is lying!' 
The question is, what are B and C?

First of all, lets simplify the statements. C's statement can be simplified to 'B is a knave.'

The formalization is given. Note that for the statement of B, if B where telling the truth then A indeed made such a statement which is the statement 'I am a Knave' and the formalization of that is 'A ∈ Knight ↔ A ∈ Knave'. Use IamKnave.
"

-- prob 26
Statement
  {inst : DecidableEq K}
  (Knight : Finset K ) (Knave : Finset K)
(h : Knight ∩ Knave = ∅ )
(h1 : A ∈ Knight ∨ A ∈ Knave ) 
(h2: B ∈ Knight ∨ B ∈ Knave )
(stB : B ∈ Knight ↔ ( A ∈ Knight ↔ A ∈ Knave  ) )
(stBn : B ∈ Knave ↔ ¬( A ∈ Knight ↔ A ∈ Knave  ) )
(stC : C ∈ Knight ↔ B ∈ Knave)
 : B ∈ Knave ∧ C ∈ Knight := by{
  -- much neater solution, very short and nice. book solution
  have : ¬ (A ∈ Knight ↔ A ∈ Knave ) := by 
  {
    intro 
    exact IamKnave h h1 a
  } 
  have BKnave := stBn.mpr this
  have CKnight := stC.mpr BKnave
  exact And.intro BKnave CKnight
}

#check not_iff_self
#check iff_false
#check iff_iff_implies_and_implies
#check and_imp

example
  {inst : DecidableEq K}
  (Knight : Finset K ) (Knave : Finset K)
(h : Knight ∩ Knave = ∅ )
(h1 : A ∈ Knight ∨ A ∈ Knave ) 
(h2: B ∈ Knight ∨ B ∈ Knave )
-- instead of stB and stnB, we can use ↔ and the knowledge of negating both sides and all that
(stB : B ∈ Knight ↔ ( A ∈ Knight ↔ A ∈ Knave  ) )
(stC : C ∈ Knight ↔ B ∈ Knave)
 : B ∈ Knave ∧ C ∈ Knight := by{
 -- have this as its own level... 
 -- can i do this with one simp comamnd?
  -- should change goal to ¬(A ∈ Knight ↔ A ∈ Knave) 
  -- truth value variant first then this(?)
  have : ¬(A ∈ Knight ↔ A ∈ Knave ) := by 
    rw [inleft_notinrightIff h1 h]
    exact not_iff_self

  rw [iff_false_right this] at stB
  rw [notinleft_inrightIff h2 h] at stB
  constructor
  · assumption

  · rw [stC]
    assumption

   
  }

Conclusion 
"
"
