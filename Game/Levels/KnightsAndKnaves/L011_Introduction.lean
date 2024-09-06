import Game.Metadata
example
  --sets
  (Knight : Set K ) (Knave : Set K)
(h : Knight ∩ Knave = ∅ )
(h1 : A ∈ Knight ∨ A ∈ Knave ) 
(h2: B ∈ Knight ∨ B ∈ Knave )
--(h3: C ∈ Knight ∨ C ∈ Knave )
-- instead of stB and stnB, we can use ↔ and the knowledge of negating both sides and all that
(stB : B ∈ Knight ↔ ( A ∈ Knight ↔ A ∈ Knave  ) )
(stC : C ∈ Knight ↔ B ∈ Knave)
 : B ∈ Knave ∧ C ∈ Knight := by{
 -- have this as its own level...
  have : (A ∈ Knight ↔ A ∈ Knave )↔ False := by 
    constructor
    · rw [iff_iff_implies_and_implies]
      #check and_imp
      rw [and_imp]
      intro kkn
      intro knk
      have AOr := h1
      cases h1
      · have kn := kkn h_1
      -- make a thm A ∈ Knight → A ∈ Knave → False
        rw [Knave_NotKnightIff h AOr] at kn
        contradiction
      · have k := knk h_1 
        rw [Knave_NotKnightIff h AOr] at h_1
        contradiction

    · apply False.elim 

-- this is the solution!!!! much shorter... the previous part would be in its own level.
  rw [this] at stB
  #check iff_false
  rw [iff_false] at stB
  rw [NotKnight_KnaveIff h h2] at stB
  constructor 
  · assumption
  · rw [stC.symm] at stB
    assumption
 }

