-- Knights And Knaves

import Mathlib.Data.Set.Basic
--import Mathlib
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Basic
--- helper

--theorem notleft_right (h : P ∨ Q) (np : ¬P)
--  : Q := by
--
--  {
--  /-
--    apply Or.elim (Classical.em Q)
--    intro hQ
--    assumption 
--
--    intro hnQ 
--    have := And.intro np hnQ
--    rw [not_or.symm] at this
--    contradiction
--    -/
--  cases h
--  · contradiction
--  · assumption
--  }


theorem notleft_right {P Q : Prop} (Or : P ∨ Q)(notleft : ¬P) : Q := by 
  cases Or
  contradiction
  assumption
theorem notright_left {P Q : Prop} (Or : P ∨ Q)(notleft : ¬Q) : P := by 
  cases Or
  assumption
  contradiction


-- notice that this is a direct adaptation of notleft_right, this theorem needs to be made clear however to make sure the user knows.
-- note : ∉ is the same as ¬ (∈) 

--NotKnight_Knave.{u_1} {K : Type u_1} {A : K} {Knight Knave : Set K} (h : Knight ∩ Knave = ∅)
--  (h1 : A ∈ Knight ∨ A ∈ Knave) (h' : A ∉ Knight) : A ∈ Knave
theorem notinleft_inright
  --sets
  {A : K}
  {left : Finset K} {right : Finset K}
  (LeftorRight : A ∈ left ∨ A ∈ right)
(h' : A ∉ left) : A ∈ right := by
  exact notleft_right LeftorRight h'

theorem notinright_inleft
  --sets
  {A : K}
  {left : Finset K} {right : Finset K}
  (LeftorRight : A ∈ left ∨ A ∈ right)
(h' : A ∉ right) : A ∈ left := by
  exact notright_left LeftorRight h'

-------------------



theorem inleft_notinright
  --sets
  [inst : DecidableEq K]
  {left : Finset K} {right : Finset K}
(h : left ∩ right = ∅ )
(h' : A ∈ left) : A ∉ right := by
  intro a 
  #check Finset.mem_inter_of_mem
  have := Finset.mem_inter_of_mem h' a
  rw [h] at this
  contradiction

theorem inright_notinleft
  --sets
  [inst : DecidableEq K]
  {left : Finset K} {right : Finset K}
(h : left ∩ right = ∅ )
(h' : A ∈ right) : A ∉ left := by
  intro a 
  have := Finset.mem_inter_of_mem h' a
  rw [Finset.inter_comm] at h
  rw [h] at this
  contradiction

  
theorem notinleft_inrightiff
  --sets
  {inst : DecidableEq K}
  {A : K}
  {left : Finset K} {right : Finset K}
  (LeftorRight : A ∈ left ∨ A ∈ right)
  (h : left ∩ right = ∅)
: A ∉ left ↔  A ∈ right := by
  constructor
  · exact notinleft_inright LeftorRight
  · exact inright_notinleft h  

theorem disjoint {inst : DecidableEq Inhabitant}  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
(h : Knight ∩ Knave = ∅ )
(hk : A ∈ Knight)
(hkn : A ∈ Knave)  : False := by 
  have := Finset.mem_inter_of_mem hk hkn 
  rw [h] at this
  contradiction
--- helper

theorem disjointfinset   {Knight : Finset K} {Knave : Finset K}
  [inst : DecidableEq K]
(h : Knight ∩ Knave = ∅ )
(hk : A ∈ Knight)
(hkn : A ∈ Knave)  : False := by 
  have := Finset.mem_inter.mpr (And.intro hk hkn )
  rw [h] at this
  contradiction

theorem IamKnave
  --sets
  {A : Inhabitant}
  [inst : DecidableEq Inhabitant]
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
(h : Knight ∩ Knave = ∅ )
(h1 : A ∈ Knight ∨ A ∈ Knave )
(stA : A ∈ Knight  ↔ (A ∈ Knave) )
  : False := by

  {
    rcases h1 with AKnight|AKnave

    · have := stA.mp AKnight
      exact disjoint h AKnight this
    
    · have := stA.mpr AKnave
      exact disjoint h this AKnave
  }

-- shouldn't this be iff to alow rewrites... instead of `have`
#check inleft_notinright
-- this theorem is redundant, it is the same as inleft_notinright if you rename things appropriately. We live it however because the semantics (from the name) are clearer.
theorem Knight_NotKnave
  --sets
  [inst : DecidableEq Inhabitant]
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
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
    -- this
    --by_contra
    --exact disjoint h h' a
    exact inleft_notinright h h'
  }

--theorem Knight_NotNormal
--{Knight : Finset Inhabitant} 
--{Normal : Finset Inhabitant} 
--{inst : DecidableEq Inhabitant}
--(hKN : Knight ∩ Normal = ∅ )
--(AKnight : A ∈ Knight) : A ∉ Normal := by
--  #check inleft_notinright
--  exact inleft_notinright hKN AKnight

-- redundant inright and inleft can do it.
--theorem Knave_NotKnight
--  -- make them required arguments then make variables above it so user only puts h'
--  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
--  {inst : DecidableEq Inhabitant}
--(h : Knight ∩ Knave = ∅ )
--(h' : A ∈ Knave)
--  : ¬ (A ∈ Knight) := by
--
--  {
--    exact inright_notinleft h h'
--  }
--
--theorem Knave_NotNormal
--{inst : DecidableEq K}
--{Knave : Finset K}
--{Normal : Finset K} 
--(hKnN : Knave ∩ Normal = ∅ )
--(hk : A ∈ Knave) : A ∉ Normal := by
--  exact inleft_notinright hKnN hk
--  
--theorem Normal_NotKnight
--{Knight : Set K} {Knave : Set K}
--{Normal : Set K} 
--(hKnN : Knight ∩ Normal = ∅ )
--(hk : A ∈ Normal) : A ∉ Knight := by
--  rw [Set.inter_comm] at hKnN
--  exact disjoint hKnN hk
--
--
--theorem Normal_NotKnave
--{Knight : Set K} {Knave : Set K}
--{Normal : Set K} 
--(hKnN : Knave ∩ Normal = ∅ )
--(hk : A ∈ Normal) : A ∉ Knave := by
--  rw [Set.inter_comm] at hKnN
--  exact disjoint hKnN hk


--- not versions different for normal
theorem NotKnave_Knight 

-- notice that if B not in Knave then we don't know if B is in knight. But we want this because on our island, those are the only two options and if you arent one of those options then you are whats left...

-- you have two options, either being a knight or a knave. if you aren't a knave then the only option left is a knight. but the formalization in lean allows for B not to be a knight either, maybe its something else. The way to resolve this is to assert that B is either a knight ∨ knave.
{Knight : Finset K } {Knave : Finset K}
--{h1 : Xor' (A ∈ Knight) (B ∈ Knave) }
--{h2: Xor' (B ∈ Knight)  (B ∈ Knave) }
(h' : B ∈ Knight ∨ B ∈ Knave)
(h'' : ¬ (B ∈ Knave))
  :  B ∈ Knight := by
{
  exact notinright_inleft h' h''

  -- disjunctive syllogism here... if you arent left then you are right.
  --cases h'
  --assumption
  --contradiction
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



--theorem NotKnight_Knave
--  --sets
--{Knight : Set K} {Knave : Set K}
--(h : Knight ∩ Knave = ∅ )
--(h1 : A ∈ Knight ∨ A ∈ Knave)
--(h' : ¬ (A ∈ Knight) )
--: A ∈ Knave  := by
--
--  {
--    cases h1 
--    contradiction
--    assumption
--  }


-- simplifying the conditions, also the Xor' conditions won't be necessary after the notKnave_Knave (etc ...) stuff
theorem XorToOr {inst : DecidableEq Inhabitant}{Knight : Finset Inhabitant } {Knave : Finset Inhabitant} (A : Inhabitant)
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
      exact inleft_notinright h h_1
    · right
      constructor
      assumption
      exact inright_notinleft h h_1

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
{inst : DecidableEq K}
{Knight : Finset K} 
{Knave : Finset K} 
{Normal : Finset K} 
(hKN : Knight ∩ Normal = ∅ )
(h' : A ∈ Knight ∨ A ∈ Knave ∨ A ∈ Normal)
(hnN :A ∉ Normal): A ∈ Knight ∨ A ∈ Knave:= by
  rw [←or_assoc] at h'
  exact notright_left h' hnN
  
  

-- needs Knight_NotKnave, Knight_NotNormal

theorem Knight_NotKnaveNotNormal
{inst : DecidableEq K}
{Knight : Finset K} {Knave : Finset K}
{Normal : Finset K} 
{hKKn : Knight ∩ Knave = ∅ }
{hKN : Knight ∩ Normal = ∅ }
{hKnN : Knave ∩ Normal = ∅ }
(hk : A ∈ Knight)
: A ∉ Knave ∧ A ∉ Normal := by 
  constructor
  exact inleft_notinright hKKn hk
  exact inleft_notinright hKN hk

theorem NotKnave_KnightNormal  
{Knight : Finset K} {Knave : Finset K}
{Normal : Finset K} 
[inst : DecidableEq K]
(hKKn : Knight ∩ Knave = ∅ )
(hKN : Knight ∩ Normal = ∅ )
(hKnN : Knave ∩ Normal = ∅ )
(h' : A ∈ Knight ∨ A ∈ Knave ∨ A ∈ Normal)
(h : A ∉ Knave) : A ∈ Knight ∨ A ∈ Normal := by {
  cases h'
  · left
    assumption
  · cases h_1
    · contradiction
    · right
      assumption
}



#check notinleft_inrightiff

theorem inright_notinleftIff
  --sets
  {inst : DecidableEq K}
  {A : K}
  {left : Finset K} {right : Finset K}
  (LeftorRight : A ∈ left ∨ A ∈ right)
  (h : left ∩ right = ∅)
: A ∈ right ↔  A ∉ left := by
  symm
  exact notinleft_inrightiff LeftorRight h

theorem inleft_notinrightIff
  --sets
  {inst : DecidableEq K}
  {A : K}
  {left : Finset K} {right : Finset K}
  (LeftorRight : A ∈ left ∨ A ∈ right)
  (h : left ∩ right = ∅)
: A ∉ left ↔  A ∈ right := by
  symm
  exact inright_notinleftIff LeftorRight h

@[simp]
theorem Knight_NotKnaveIff
  --sets
  {inst : DecidableEq K}
  {Knight : Finset K} {Knave : Finset K}
(h : Knight ∩ Knave = ∅ )
(h' : A ∈ Knight ∨ A ∈ Knave)
--{h1 : Xor' (A ∈ Knight) (A ∈ Knave) } {h2: Xor' (B ∈ Knight)  (B ∈ Knave) } (h' : A ∈ Knight)
 
  : A ∈ Knight ↔ A ∉ Knave := by
  #check notinleft_inrightiff
  #check inleft_notinrightIff

  symm
  rw [or_comm] at h'
  rw [Finset.inter_comm] at h
  exact inleft_notinrightIff h' h
  
  --#check not_iff_not
  --constructor 
  --exact inleft_notinright h
  --exact notinright_inleft h' 


@[simp]
theorem NotKnight_KnaveIff
  --sets
{inst : DecidableEq K}
{Knight : Finset K} {Knave : Finset K}
(h : Knight ∩ Knave = ∅ )
(h' : A ∈ Knight ∨ A ∈ Knave)
 : ¬ (A ∈ Knight) ↔ A ∈ Knave  := by

  {
   #check Knight_NotKnaveIff
   #check not_iff_not.mpr
   #check not_iff
   rw [not_iff.symm]
   rw [Knight_NotKnaveIff h h']
   exact not_iff_self
   --have := not_iff (Knight_NotKnaveIff h h')

   --exact not_iff_not Knight_NotKnaveIff h h'
  }





@[simp]
theorem Knave_NotKnightIff
  --sets
  -- make them required arguments then make variables above it so user only puts h'
  {inst : DecidableEq K}
  {Knight : Finset K} {Knave : Finset K}
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
    #check inright_notinleftIff
    exact Iff.symm (NotKnight_KnaveIff h h')

    --constructor
    --exact Knave_NotKnight h 
    --exact NotKnight_Knave h h'
  }



@[simp]
theorem NotKnave_KnightIff

-- notice that if B not in Knave then we don't know if B is in knight. But we want this because on our island, those are the only two options and if you arent one of those options then you are whats left...

-- you have two options, either being a knight or a knave. if you aren't a knave then the only option left is a knight. but the formalization in lean allows for B not to be a knight either, maybe its something else. The way to resolve this is to assert that B is either a knight ∨ knave.
  {inst : DecidableEq K}
  {Knight : Finset K} {Knave : Finset K}
(h : Knight ∩ Knave = ∅ )
--{h1 : Xor' (A ∈ Knight) (B ∈ Knave) }
--{h2: Xor' (B ∈ Knight)  (B ∈ Knave) }
(h' : B ∈ Knight ∨ B ∈ Knave)
: ¬ (B ∈ Knave) ↔  B ∈ Knight := by

  exact Iff.symm (inleft_notinrightIff h h')
  --constructor
  --exact NotKnave_Knight h h'
  --exact Knight_NotKnave h 


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

theorem NotKnightNormal_Knave 
{Knight : Finset K} {Knave : Finset K}
{Normal : Finset K} 
[inst : DecidableEq K]
--(hKN : Knight ∩ Normal = ∅ )
(Or : A ∈ Knight ∨ A ∈ Knave ∨ A ∈ Normal)
(h : A ∉ Knight)
(h' : A ∉ Normal)
: A ∈ Knave := by 
  cases Or 
  · contradiction
  · cases h_1 
    · assumption
    · contradiction

theorem NotKnaveNormal_Knight
{Knight : Finset K} {Knave : Finset K}
{Normal : Finset K} 
[inst : DecidableEq K]
--(hKN : Knight ∩ Normal = ∅ )
(Or : A ∈ Knight ∨ A ∈ Knave ∨ A ∈ Normal)
(h : A ∉ Knave)
(h' : A ∉ Normal) : A ∈ Knight := by 
  cases Or
  · assumption
  · cases h_1
    · contradiction
    · contradiction

theorem NotKnightKnave_Normal
{Knight : Finset K} {Knave : Finset K}
{Normal : Finset K} 
[inst : DecidableEq K]
--(hKN : Knight ∩ Normal = ∅ )
(Or : A ∈ Knight ∨ A ∈ Knave ∨ A ∈ Normal)
(h : A ∉ Knight)
(h' : A ∉ Knave)
: A ∈ Normal := by 
  cases Or
  · contradiction
  · cases h_1
    · contradiction
    · assumption
--OneNormal : Normal.card = 1
--ANormal : A ∈ Normal
--CNormal : C ∈ Normal
theorem card_eq {Normal : (Finset K)} (h : Normal.card =1) (ANormal : A ∈ Normal) ( BNormal : B ∈ Normal) : A=B := by 
  have := Nat.le_of_eq h
  rw [Finset.card_le_one_iff] at this
  exact this ANormal BNormal

theorem full  
{S : Finset K} 
--[inst : DecidableEq K]
--(hKKn : Knight ∩ Knave = ∅ )
--(hKN : Knight ∩ Normal = ∅ )
--(hKnN : Knave ∩ Normal = ∅ )
--(h' : A ∈ Knight ∨ A ∈ Knave ∨ A ∈ Normal)
{B : K}
(AinS: A ∈ S)
(One : S.card =1)
(AneB : A ≠ B)
: B ∉ S := by {
  by_contra BinS
  exact AneB (card_eq One AinS BinS)
}
