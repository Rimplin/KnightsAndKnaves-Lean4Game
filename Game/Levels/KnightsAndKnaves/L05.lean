import Game.Metadata
--import Game.Levels.KnightsAndKnavesLemmas.L02_Knight_NotKnave
--import Game.Levels.KnightsAndKnavesLemmas.L02_NotKnave_Knight
--import Game.Levels.KnightsAndKnavesLemmas.L03_Knave_NotKnight
--import Game.Levels.KnightsAndKnavesLemmas.L04_NotKnight_Knave



--variable (Inhabitant : Type)
--#check (Sum Inhabitant Inhabitant)
--variable (Knight Knave : Type)
--variable (A : Sum Knight Knave)
--inductive A where
--| Knight
--| Knave

-- Define a sum type that can be either an integer or a boolean
--inductive Inhabitant
--| int 
--| bool 
--variable (B : Knight)
--example : ( Sum.inl A ∈ Knight) := by
--  cases A 
  
--example : 2=2 := by sorry
--variable (Knight: Type) (Knave : Type)
--def Inhabitant := (Sum Knight Knave)
--#check Inhabitant
--example (A : Inhabitant Knight Knave) : 2=2  := sorry

/-
inductive Weekday where
  | sunday : Weekday
  | monday : Weekday
  | tuesday : Weekday
  | wednesday : Weekday
  | thursday : Weekday
  | friday : Weekday
  | saturday : Weekday
inductive Inhabitant where 
| Knight'
| Knave'

#check Inhabitant.Knave'
#check Inhabitant.Knight'
example (A : Inhabitant) : 2=2 :=  
  match A with 
  | Knight' => sorry
  | Knave' => sorry
-/
-- problem 28
variable (Knight : Set K) (Knave : Set K)

example
  --sets
{h : Knight ∩ Knave = ∅ }
{h1 : Xor' (A ∈ Knight) (A ∈ Knave) }
{h2: Xor' (B ∈ Knight)  (B ∈ Knave) }
{stA : A ∈ Knight  ↔ ((A ∈ Knave) ∨ (B ∈ Knave)) }
  : A ∈ Knight ∧ B ∈ Knave := by
  {
    --#check Knave_NotKnight

    have this := h1
    unfold Xor' at h1
    cases h1 
    · have := stA.mp h_1.left
      cases this 
        -- having Xor and all that might get a rewrite so this would need to change
      · sorry--have := Knave_NotKnight h this h_2
        ----have := @Knave_NotKnight K A Knight Knave h this h_2
        --exfalso 
        --exact this h_1.left

      · sorry
    · sorry
  }


example (h : p ↔ q) (h' : q ↔ r) : p ↔ r := by 
  rw [h'] at h
  -- loss of information
  rw [h'] at h'
  assumption
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

-- problem 27
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

