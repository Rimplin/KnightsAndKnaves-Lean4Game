import Game.Metadata

-- break up every problem into multiple levels explaining the reasoning behind the solution
-- problem 26, what is the name of this book
example
  --sets
  (Knight : Set K ) (Knave : Set K)
(h : Knight ∩ Knave = ∅ )
(h1 : Xor' (A ∈ Knight) (A ∈ Knave) ) 
(h2: Xor' (B ∈ Knight)  (B ∈ Knave) )
(h3: Xor' (C ∈ Knight)  (C ∈ Knave) )
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

-- in this problem, we cannot know what `A` is, should this be demonstrated in a level? some helpful lessons are present.
example
  --sets
  (Knight : Set K ) (Knave : Set K)
(h : Knight ∩ Knave = ∅ )
(h1 : Xor' (A ∈ Knight) (A ∈ Knave) ) 
(h2: Xor' (B ∈ Knight)  (B ∈ Knave) )
(h3: Xor' (C ∈ Knight)  (C ∈ Knave) )
(stB : (B ∈ Knight) → (A ∈ Knight →
  (A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knight) ) )
(stBn : (B ∈ Knave) → (A ∈ Knight → ¬ (
  (A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knight)) ) )
(stC : ( C ∈ Knight → B ∈ Knave) )
(stnC : ( C ∈ Knave → B ∈ Knight) )
  : B ∈ Knave ∧ C ∈ Knight
  := by 
    have : B ∈ Knight ∧ C ∈ Knave ∨ B ∈ Knave ∧ C ∈ Knight := by 
      cases h3
      exact Or.inr (⟨stC h_1.left ,h_1.left⟩ )
      exact Or.inl (⟨stnC h_1.left ,h_1.left⟩ )


    rcases this with ⟨BKnight,CKnave⟩|⟨_,_⟩ 
    · have BKnight := eq_true BKnight
      have CKnave := eq_true CKnave
      simp [BKnight,CKnave] at stB
      -- need to get BnKnave from BKnight and so on.... include these in the world
      --rw [true_implies] at stB
      sorry
    · exact ⟨left,right⟩ 
#check eq_true

example
  --sets
  (Knight : Set K ) (Knave : Set K)
(h : Knight ∩ Knave = ∅ )
(h1 : Xor' (A ∈ Knight) (A ∈ Knave) ) 
(h2: Xor' (B ∈ Knight)  (B ∈ Knave) )
(h3: Xor' (C ∈ Knight)  (C ∈ Knave) )
: sorry:= by
  sorry


variable (Knight : Set K ) (Knave : Set K)
(h : Knight ∩ Knave = ∅ )
(h1 : Xor' (x ∈ Knight) (x ∈ Knave) ) 
(h2: Xor' (y ∈ Knight)  (y ∈ Knave) )
(h3: Xor' (z ∈ Knight)  (z ∈ Knave) )

open Set
#check not_mem_empty


example
  --sets
(stx : x ∈ Knight → x ∈ Knave)
(stxn : x ∈ Knave → ¬(x ∈ Knave) ) : x ∈ Knave  := by
{
  rcases h1 with ⟨xKnight,xnKnave⟩|⟨xKnave,xnKnight⟩  
  · have xKnave := stx xKnight
    contradiction
  · have xnKnave := stxn xKnave
    contradiction
    
}

example
  --sets
(stx : x ∈ Knight → x ∈ Knave)
(stxn : x ∈ Knave → ¬(x ∈ Knave) ) : x ∈ Knight  := by
{
  rcases h1 with ⟨xKnight,xnKnave⟩|⟨xKnave,xnKnight⟩  
  · have xKnave := stx xKnight
    contradiction
  · have xnKnave := stxn xKnave
    contradiction
    
}
