-- Knights And Knaves

import Mathlib.Data.Set.Basic


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
    have := Set.mem_inter a h'
    rw [h] at this
    contradiction
  }

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
    have := Set.mem_inter h' a
    rw [h] at this
    contradiction
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
