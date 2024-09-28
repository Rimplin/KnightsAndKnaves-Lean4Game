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
  --sets
  (Knight : Set K ) (Knave : Set K)
(h : Knight ∩ Knave = ∅ )
(h1 : A ∈ Knight ∨ A ∈ Knave ) 
(h2: B ∈ Knight ∨ B ∈ Knave )
--(h3: C ∈ Knight ∨ C ∈ Knave )
-- instead of stB and stnB, we can use ↔ and the knowledge of negating both sides and all that
(stB : B ∈ Knight ↔ ( A ∈ Knight ↔ A ∈ Knave  ) )
(stBn : B ∈ Knave ↔ ¬( A ∈ Knight ↔ A ∈ Knave  ) )
(stC : C ∈ Knight ↔ B ∈ Knave)
 : B ∈ Knave ∧ C ∈ Knight := by{
  -- much neater solution, very short and nice
  have : ¬ (A ∈ Knight ↔ A ∈ Knave ) := by 
  {
    intro 
    exact IamKnave h h1 a
    --intro stA
    --rw [Knight_NotKnaveIff h h1] at stA
    --simp at stA
  } 
  have BKnave := stBn.mpr this
  have CKnight := stC.mpr BKnave
  exact And.intro BKnave CKnight

--  have : (A ∈ Knight ↔ A ∈ Knave )↔ False := by 
--    #check not_iff_self
--    --rw [Knight_NotKnaveIff h h1] 
--    #check not_iff_self
--    constructor 
--    · intro stA
--      exact IamKnave h h1 stA
--    · exact False.elim
  --rw [this] at stB
  --#check iff_false
  --rw [iff_false] at stB
  --rw [NotKnight_KnaveIff h h2] at stB
  --constructor 
  --· assumption
  --· rw [stC.symm] at stB
  --  assumption



  --------------------------
    --constructor
    --· rw [iff_iff_implies_and_implies]
    --  #check and_imp
    --  rw [and_imp]
    --  intro kkn
    --  intro knk
    --  have AOr := h1
    --  cases h1
    --  · have kn := kkn h_1
    --  -- make a thm A ∈ Knight → A ∈ Knave → False
    --    rw [Knave_NotKnightIff h AOr] at kn
    --    contradiction
    --  · have k := knk h_1 
    --    rw [Knave_NotKnightIff h AOr] at h_1
    --    contradiction

    --· apply False.elim 

-- this is the solution!!!! much shorter... the previous part would be in its own level.
 }



example
  (Knight : Set K ) (Knave : Set K)
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
    rw [Knight_NotKnaveIff h h1]
    exact not_iff_self

  rw [iff_false_right this] at stB
  rw [NotKnight_KnaveIff h h2] at stB
  constructor
  · assumption

  · rw [stC]
    assumption

   
  }

Conclusion 
"
"
