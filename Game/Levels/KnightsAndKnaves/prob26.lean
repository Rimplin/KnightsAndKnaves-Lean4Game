import Game.Metadata
-- break up every problem into multiple levels explaining the reasoning behind the solution
-- problem 26, what is the name of this book
-- notice that from the statement of B we can know that B is a knave, and then C correctly asserted that B is a knave so we get that C is a knight.(if someone tells the truth then they must be a knight because there is no other option, if there was someone that sometimes lies or tells the truth we can't know, therefore `iff` is more appropriate here and implication is more appropriate when such a character is present)

#check imp_false
example
  --sets
  (Knight : Set K ) (Knave : Set K)
(h : Knight ∩ Knave = ∅ )
(h1 : Xor' (A ∈ Knight) (A ∈ Knave) ) 
(h2: Xor' (B ∈ Knight)  (B ∈ Knave) )
(h3: Xor' (C ∈ Knight)  (C ∈ Knave) )
-- instead of stB and stnB, we can use ↔ and the knowledge of negating both sides and all that
(stB : B ∈ Knight → ( (A ∈ Knight → A ∈ Knave) ∧ (A ∈ Knave → A ∈ Knight) ))
(stnB : B ∈ Knave → ¬( (A ∈ Knight → A ∈ Knave) ∧ (A ∈ Knave → A ∈ Knight) ))
(stC : C ∈ Knight → B ∈ Knave)
-- should be ¬ (B ∈ Knave) instead of B ∈ Knight, but they are logically equivalent. prove that, need to examine and add levels for this.
(stnC : C ∈ Knave → B ∈ Knight)
 : B ∈ Knave ∧ C ∈ Knight := by{
  rcases h3 with ⟨CKnight,CnKnave⟩|⟨CKnave,CnKnight⟩  
  · have := stC CKnight
    constructor
    assumption; assumption
  · -- here we want to prove that C is a knight but we know that C is not a knight, so we will have to derive some contradiction to get the goal we want
    have := stnC CKnave
    have ⟨KnightKnave,KnaveKnight⟩ := stB this
    rcases h1 with ⟨AKnight,AnKnave⟩|⟨AKnave,AnKnight⟩  
    · have := KnightKnave AKnight
      contradiction
    · have := KnaveKnight AKnave
      contradiction
  }

example : A ∈ Knight ↔ A ∈ Knight ∧ B ∈ Knight := by 
  simp 
  #check imp_and
  sorry

-- problem 26
-- new formalization
#check XorToOr

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
 -- iff sometimes can be confusing , manipulate it
  #check iff_iff_implies_and_implies
  -- (p → q ∧ ¬p → ¬q)  ↔ (p ↔ q)
  #check iff_iff_and_or_not_and_not
  #check iff_and_self
  #check iff_self_and
  #check iff_iff_not_or_and_or_not
  #check IffToIf
  have :=IffToIf stB
  have ⟨forward,backward⟩ := stB
  --rw [iff_iff_implies_and_implies] at stB
  --rw [not_iff_not.symm] at stB
  --nth_rw 2 [not_iff_not.symm] at stB

  cases h2
  · rw [stB] at h_1
    cases h1
    · have := h_1.mp h_2
      have this2:= Set.mem_inter h_2 this
      rw [h] at this2
      contradiction
    · have := h_1.mpr h_2 
      have this2:= Set.mem_inter this h_2
      rw [h] at this2
      contradiction
  · constructor
    assumption
    rw [stC.symm] at h_1
    assumption
}




