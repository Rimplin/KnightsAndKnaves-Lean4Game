-- Knights And Knaves

import Mathlib.Data.Set.Basic

--- helper
theorem disjoint   {Knight : Set K} {Knave : Set K}
(h : Knight ∩ Knave = ∅ )
(hk : A ∈ Knight)
(hkn : A ∈ Knave)  : False := by 
  have := Set.mem_inter hk hkn 
  rw [h] at this
  contradiction
--- helper

-- shouldn't this be iff to alow rewrites... instead of `have`
theorem Knight_NotKnave
  --sets
  {Knight : Set K} {Knave : Set K}
(h : Knight ∩ Knave = ∅ )
--{h1 : Xor' (A ∈ Knight) (A ∈ Knave) } {h2: Xor' (B ∈ Knight)  (B ∈ Knave) } (h' : A ∈ Knight)
(h' : A ∈ Knight)
  : A ∉ Knave := by

  {
   -- unfold Xor' at h1
   -- cases h1
   -- · exact h_1.right
   -- · exfalso
   --   exact h_1.right h'

    -- eliminate h1 , h2 and do by_contra
    by_contra
    exact disjoint h h' a
  }

theorem Knight_NotNormal
{Knight : Set K} 
{Normal : Set K} 
(hKN : Knight ∩ Normal = ∅ )
(hk : A ∈ Knight) : A ∉ Normal := by
  exact disjoint hKN hk


theorem Knave_NotKnight
  --sets
  -- make them required arguments then make variables above it so user only puts h'
  {Knight : Set K} {Knave : Set K}
(h : Knight ∩ Knave = ∅ )
--(h1 : Xor' (A ∈ Knight) (A ∈ Knave) )
(h' : A ∈ Knave)
  : ¬ (A ∈ Knight) := by

  {
    -- h1
    --unfold Xor' at h1 
    --cases h1 
    --· exfalso
    --  exact h_1.right h'
    --· exact h_1.right
    by_contra
    exact disjoint h a h'
  }

theorem Knave_NotNormal
{Knight : Set K} {Knave : Set K}
{Normal : Set K} 
(hKnN : Knave ∩ Normal = ∅ )
(hk : A ∈ Knave) : A ∉ Normal := by
  exact disjoint hKnN hk

theorem Normal_NotKnight
{Knight : Set K} {Knave : Set K}
{Normal : Set K} 
(hKnN : Knight ∩ Normal = ∅ )
(hk : A ∈ Normal) : A ∉ Knight := by
  rw [Set.inter_comm] at hKnN
  exact disjoint hKnN hk


theorem Normal_NotKnave
{Knight : Set K} {Knave : Set K}
{Normal : Set K} 
(hKnN : Knave ∩ Normal = ∅ )
(hk : A ∈ Normal) : A ∉ Knave := by
  rw [Set.inter_comm] at hKnN
  exact disjoint hKnN hk


--- not versions different for normal
theorem NotKnave_Knight 

-- notice that if B not in Knave then we don't know if B is in knight. But we want this because on our island, those are the only two options and if you arent one of those options then you are whats left...

-- you have two options, either being a knight or a knave. if you aren't a knave then the only option left is a knight. but the formalization in lean allows for B not to be a knight either, maybe its something else. The way to resolve this is to assert that B is either a knight ∨ knave.
{Knight : Set K } {Knave : Set K}
(h : Knight ∩ Knave = ∅ )
--{h1 : Xor' (A ∈ Knight) (B ∈ Knave) }
--{h2: Xor' (B ∈ Knight)  (B ∈ Knave) }
(h' : B ∈ Knight ∨ B ∈ Knave)
(h'' : ¬ (B ∈ Knave))
  :  B ∈ Knight := by
{
  -- disjunctive syllogism here... if you arent left then you are right.
  cases h'
  assumption
  contradiction
  -- use this exercise to introduce disjucntive syllogism and say that this reasoning is true in general(if needed by future levels).

  -- explain precedence so users can understand the unfolded result.
--  unfold Xor' at h1

  -- introduce ¬¬ p → p
  -- first approach by contradiction
  /-
  by_contra h''
  have h' := eq_false h'
  have h'' := eq_false h''
  rw [h',h''] at h1
  simp at h1
  -/

  -- second approach, direct
  --have h' := eq_false h'
  --rw [h'] at h1
  --simp at h1
  --assumption

}



theorem NotKnight_Knave
  --sets
{Knight : Set K} {Knave : Set K}
(h : Knight ∩ Knave = ∅ )
(h1 : A ∈ Knight ∨ A ∈ Knave)
(h' : ¬ (A ∈ Knight) )
: A ∈ Knave  := by

  {
    cases h1 
    contradiction
    assumption
  }


-- simplifying the conditions, also the Xor' conditions won't be necessary after the notKnave_Knave (etc ...) stuff
theorem XorToOr {Knight : Set Inhabitants } {Knave : Set Inhabitants} (A : Inhabitants)
(h : Knight ∩ Knave = ∅ ) : Xor' (A ∈ Knight) (A ∈ Knave) ↔ A ∈ Knight ∨ A ∈ Knave := by 
  constructor
  unfold Xor' at *
  · intro h'
    cases h'
    · exact Or.inl (h_1.left)
    · exact Or.inr (h_1.left)

  · intro h'
    unfold Xor'
    cases h'
    · left
      constructor
      assumption
      exact Knight_NotKnave h h_1
    · right
      constructor
      assumption
      exact Knave_NotKnight h h_1

-- from implication to if and only if

theorem IfToIff (h : p → q) (h' : ¬p → ¬q) : p ↔ q := by 
  constructor
  · assumption
  · intro hq
    exact (Function.mtr h') hq
theorem IffToIf (h : p ↔ q) : (p → q) ∧ (¬p → ¬q) := by 
  constructor
  · exact h.mp
  · exact Function.mt (h.mpr)



--- Knights and Knaves and Normal
theorem Knight_NotKnaveNotNormalcont
{Knight : Set K} {Knave : Set K}
{Normal : Set K} 
(h : Knight ∩ Normal = ∅ )
(hk : A ∈ Knight)
(hkn : A ∈ Normal)  : False := by 
  exact disjoint h hk hkn 

-- Knight
-- Knave
-- Normal
-- maybe should do Knight_NotKnave, Knight_NotNormal etc... and not this because this would require to input multiple arguments for the disjoint sets and also might have superflous information
-- enumerate all of them then put all the iff versions at the end after the normal ones, because the iff versions can be proven using the normal ones.


theorem NotNormal_Knight
{Knight : Set K} 
{Knave : Set K} 
{Normal : Set K} 
(hKN : Knight ∩ Normal = ∅ )
(h' : A ∈ Knight ∨ A ∈ Knave ∨ A ∈ Normal)
(hnN :A ∉ Normal): A ∈ Knight ∨ A ∈ Knave:= by
  sorry
  
  





-- needs Knight_NotKnave, Knight_NotNormal

theorem Knight_NotKnaveNotNormal
{Knight : Set K} {Knave : Set K}
{Normal : Set K} 
{hKKn : Knight ∩ Knave = ∅ }
{hKN : Knight ∩ Normal = ∅ }
{hKnN : Knave ∩ Normal = ∅ }
(hk : A ∈ Knight)
: A ∉ Knave ∧ A ∉ Normal := by 
  constructor
  exact Knight_NotKnave hKKn hk
  exact Knight_NotNormal hKN hk



@[simp]
theorem Knight_NotKnaveIff
  --sets
  {Knight : Set K} {Knave : Set K}
(h : Knight ∩ Knave = ∅ )
(h' : A ∈ Knight ∨ A ∈ Knave)
--{h1 : Xor' (A ∈ Knight) (A ∈ Knave) } {h2: Xor' (B ∈ Knight)  (B ∈ Knave) } (h' : A ∈ Knight)
 
  : A ∈ Knight ↔ A ∉ Knave := by
  constructor 
  exact Knight_NotKnave  h
  exact NotKnave_Knight h h'

@[simp]
theorem NotKnight_KnaveIff
  --sets
{Knight : Set K} {Knave : Set K}
(h : Knight ∩ Knave = ∅ )
(h' : A ∈ Knight ∨ A ∈ Knave)
 : ¬ (A ∈ Knight) ↔ A ∈ Knave  := by

  {
    constructor
    · exact NotKnight_Knave h h'
    · exact Knave_NotKnight h
  }





@[simp]
theorem Knave_NotKnightIff
  --sets
  -- make them required arguments then make variables above it so user only puts h'
  {Knight : Set K} {Knave : Set K}
(h : Knight ∩ Knave = ∅ )
(h' : A ∈ Knight ∨ A ∈ Knave)
--(h1 : Xor' (A ∈ Knight) (A ∈ Knave) )
: A ∈ Knave ↔ ¬ (A ∈ Knight) := by

  {
    -- h1
    --unfold Xor' at h1 
    --cases h1 
    --· exfalso
    --  exact h_1.right h'
    --· exact h_1.right
    constructor
    exact Knave_NotKnight h 
    exact NotKnight_Knave h h'
  }



@[simp]
theorem NotKnave_KnightIff

-- notice that if B not in Knave then we don't know if B is in knight. But we want this because on our island, those are the only two options and if you arent one of those options then you are whats left...

-- you have two options, either being a knight or a knave. if you aren't a knave then the only option left is a knight. but the formalization in lean allows for B not to be a knight either, maybe its something else. The way to resolve this is to assert that B is either a knight ∨ knave.
{Knight : Set K } {Knave : Set K}
(h : Knight ∩ Knave = ∅ )
--{h1 : Xor' (A ∈ Knight) (B ∈ Knave) }
--{h2: Xor' (B ∈ Knight)  (B ∈ Knave) }
(h' : B ∈ Knight ∨ B ∈ Knave)
: ¬ (B ∈ Knave) ↔  B ∈ Knight := by
  constructor
  exact NotKnave_Knight h h'
  exact Knight_NotKnave h 


-- depending on usage, start formalizing knight knave normal problems and see what i need.
-- ahhh, this is just Knight_NotNormal 
theorem Knight_NotNormalNotIff
{Knight : Set K} {Knave : Set K}
{Normal : Set K} 
(hKN : Knight ∩ Normal = ∅ )
: A ∈ Knight → A ∉ Normal  := by
  exact Knight_NotNormal hKN

theorem Knave_NotNormalNotIff
{Knight : Set K} {Knave : Set K}
{Normal : Set K} 
(hKnN : Knave ∩ Normal = ∅ )
: A ∈ Knave → A ∉ Normal  := by
  exact Knight_NotNormal hKnN

