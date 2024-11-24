import Game.Metadata
-- break up every problem into multiple levels explaining the reasoning behind the solution

--#check imp_and

#check iff_iff_implies_and_implies
--  -- (p → q ∧ ¬p → ¬q)  ↔ (p ↔ q)
#check iff_iff_and_or_not_and_not
  #check iff_and_self
  #check iff_self_and
  #check iff_iff_not_or_and_or_not
  #check IffToIf

-- stB is not a proof, it would be just a shorthand to the proposition
--def stB : Prop := (A ∈ Knight ↔ A ∈ Knave)
--def stC : Prop := (B ∈ Knave)
---- AKnight ↔ stA ∧ BKnight ↔ stB
-- would actually look like A ∈ Knight ↔ stA A Knight Knave which is ugly, also user would have to unfold so whats the point


World "KnightsAndKnaves" 
Level 2

Title "" 

Introduction 
"
Three of the inhabitants `A`, `B`, and `C` were standing together in a garden. 

A stranger passed by and asked A, 'Are you a knight or a knave?' A answered, but rather indistinctly, so the stranger could not make out what he said. 

The stranger then asked B, 'What did A say?' B replied, 'A said that he is a knave.' At this point the third man, C, said, 'Don't believe B; he is lying!' 

The question is, what are B and C?

First of all, lets simplify the statements. C's statement can be simplified to 'B is a knave.'

The statements are:
```
B says that A said 'I am a knave'
C says that B is a knave
```

The formalization is given in the proof state.

Note that for the statement of `B`, if `B` where telling the truth then `A` indeed made such a statement which is the statement 'I am a Knave' and the formalization of that is `A ∈ Knight ↔ A ∈ Knave`. Use IamKnave.
"

#check IamKnave
-- prob 26


example {inst : DecidableEq K}
  (Knight : Finset K ) (Knave : Finset K)
(h : Knight ∩ Knave = ∅ )
(h1 : A ∈ Knight ∨ A ∈ Knave ) 
(h2: B ∈ Knight ∨ B ∈ Knave )
(stB : B ∈ Knight ↔ ( A ∈ Knight ↔ A ∈ Knave  ) )
(stBn : B ∈ Knave ↔ ¬( A ∈ Knight ↔ A ∈ Knave  ) )
(stC : C ∈ Knight ↔ B ∈ Knave)
 : B ∈ Knave ∧ C ∈ Knight := by{
  rw [( IamKnaveIffFalse h h1).symm] at stB 

  sorry 
}

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
  Hint "

We know that `A` saying 'I am a knave' leads to contradiction.

So, ¬(A ∈ Knight ↔ A ∈ Knave) is true. Using stBn we get B ∈ knave 
---------
  We know that `A` saying 'I am a knave' leads to contradiction. So assuming that 'B' is a knight would lead to contradiction. So `B` is not a knight. To arrive at this conclusion formally, first you can prove the right hand side of stBn which would then give you B ∈ Knave.

  Most of the work here has already been done, we have the following theorem from the previous level(ignoring implicit arguments): 
  IamKnave : Knight ∩ Knave = ∅ → A ∈ Knight ∨ A ∈ Knave → (A ∈ Knight ↔ A ∈ Knave) → False

  notice that ...
  "

  -- this is preferable so as not to have to use editor mode, also easier to have hints 
  #check IamKnave
  have : ¬ (A ∈ Knight ↔ A ∈ Knave ) := IamKnave h h1  
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
