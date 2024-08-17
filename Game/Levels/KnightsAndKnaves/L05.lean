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


-- create some helper theorems
-- notKnave_Knight (h : ¬ (x ∈ Knave) ) : x ∈ Knight
-- notKnight_Knave (h : ¬ (x ∈ Knight) ) : x ∈ Knave
-- Knave_notKnight
-- Knight_notKnave
-- knight_knave (h : x ∈ Knight) (h' : x ∈ Knave) : False , maybe extend contradiction to detect this...
theorem notKnave_Knight (h' : ¬ (x ∈ Knave)) : x ∈ Knight := by 
  -- explain precedence so users can understand the unfolded result.
  unfold Xor' at h1

  -- introduce ¬¬ p → p
  -- first approach by contradiction
  /-by_contra h''
  have h' := eq_false h'
  have h'' := eq_false h''
  rw [h',h''] at h1
  simp at h1
  -/

  -- second approach, direct
  have h' := eq_false h'
  rw [h'] at h1
  simp at h1
  assumption

open Set
#check not_mem_empty
/-
since this is a repeated pattern in this world, we introduce it as its own level. You need to show that having two sets being disjoint (i.e sharing no common element) and having a common element is a contradiction. This is not an obvious contradiction( like p , ¬p) for the `contradiction` tactic to work. Some work needs to be done to get to that point.
Note the theorem:
```
Set.not_mem_empty.{u} {α : Type u} (x : α) : x ∉ ∅
```
An object of this type is given to you as an assumption in this level for your convenience and this you can also directly use this theorem.  can be used freely later on.

Hint: the goal is to get something that contradicts not_mem_empty. Since x belong to Knight and Knave then it belongs to their intersection which is equal to the empty set contradiction not_mem_empty. Let's do this step by step. (Make it feel like the player discovered this:
Notice that the only information we can derive is that x is in the intersection. Do we have information about the intersection? Well yes. its empty set so x ∈ empty set. Execute the finishing blow. 

This is a common theme when using `contradiction`, sometimes contradiction can't see the 'contradiction' and manipulating the proof state would reveal this to `contradiction`.
-/
theorem knight_knave (h' : x ∈ Knight) (h'' : x ∈ Knave) : False := by 
   have := Set.mem_inter h' h''
   rw [h] at this
   have this2 : ∀ x:K, x ∉ ∅  := not_mem_empty 
   contradiction


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
