import Game.Metadata
import Game.LevelLemmas.Logical
namespace LevelLemmas
open Set

variable {K : Type}

World "KnightsAndKnaves"
Level 1

Title "Intro"

#print Xor'
#check Xor
#check not_xor

#check not_iff
#check Xor'
#check eq_true
#check Iff
#check and_iff_not_or_not
#check iff_iff_and_or_not_and_not
set_option trace.Meta.Tactic.simp true


example : (p ↔ q) ↔ (¬p ↔ ¬q) := by 
  constructor
  · intro h
  -- sol 1
    --rw [h]
  -- sol 2
    constructor
    · intro h'
      intro h''
      have := h.mpr h''
      exact h' this

    · intro h'
      intro h''
      have := h.mp h''
      exact h' this 

  · intro h'
    constructor 
    · intro h''
      have := Function.mt (h'.mpr) (not_not.mpr h'')
      rw [not_not] at this
      assumption
    · intro h''
      have := Function.mt (h'.mp) (not_not.mpr h'')
      rw [not_not] at this
      assumption

example : Xor' p q ↔ ¬(p ↔ q) := by 
  unfold Xor'

  constructor 
  · intro h
    intro h'
    rw [h'] at h
    rw [or_self] at h
    simp at h 
  · intro h
    

    by_contra h'
    rw [iff_iff_and_or_not_and_not] at h
    cases em p
    · cases em q
      · exact h (Or.inl (⟨h_1,h_2⟩ )) 
      · exact h' (Or.inl (⟨h_1,h_2⟩ )) 

    · cases em q
      · exact h' (Or.inr (⟨h_2,h_1⟩ )) 
      · exact h (Or.inr (⟨h_1,h_2⟩ )) 


    --contrapose h
    --rw [not_not]
    --constructor 
    --· intro 
    --  by_contra h'
    --  exact h (Or.inl (⟨a,h'⟩))
    --· sorry


    --rw [not_iff] at h 
    --rw [h]
Introduction 
"
# Xor
To introduce Xor, introduce as the negation of if and only if. Xor is inequivalence, Xor is such that exactly one of the propositions is truei.e exclusive or. 

# How the proof will work(cases tactic)
Take all possible cases for `x` and `y`. These cases are:
```
x ∈ Knight, y ∈ Knight
x ∈ Knight, y ∈ Knave
x ∈ Knave, y ∈ Knight
x ∈ Knave, y ∈ Knave
```
"

-- develop tactic if x in knight then x not in knave
Statement --(preamble := unfold Xor' at *)
  --sets
  (Knight : Set K ) (Knave : Set K)
  (h : Knight ∩ Knave = ∅ ) (h1 : Xor' (x ∈ Knight) (x ∈ Knave) ) (h2: Xor' (y ∈ Knight)  (y ∈ Knave) )

  -- x says y is a knight
  -- y says that x and y are of different type
  --rules of the game, i.e knights tell the truth but knaves lie
  (stx : x ∈ Knight → y ∈ Knight) (sty: y ∈ Knight → (x ∈ Knight ∧ y ∈ Knave) ∨ (x ∈ Knave ∧ y ∈ Knight) )
  (stxn : x ∈ Knave →  y ∈ Knave) (styn: y ∈ Knave → ¬ ( (x ∈ Knight ∧ y ∈ Knave) ∨ (x ∈ Knave ∧ y ∈ Knight) ) )
  : x ∈ Knave ∧ y ∈ Knave := by
  {
  -- need to teach pattern matching
  -- need to have alot of proficiency
  --unfold Xor' at *
  rcases h1 with ⟨xt,_⟩|⟨xl,_⟩ 
  -- can use clear and stuff, should explain that if the antecedent of an impliation is false then we can't conclude the conclusion wihch validates clearing stxn here because the atecedent is false.
  · clear stxn
    rcases h2 with ⟨yt,_⟩|⟨yl,_⟩  
    · have xst := stx xt
      have yst := sty yt
      rcases yst with ⟨y1,y2⟩ | ⟨y3,y4⟩
      · contradiction 
      · contradiction
    · have xst := stx xt
      contradiction
  · rcases h2 with ⟨yt,_⟩|⟨yl,_⟩  
    · have yst := sty yt 
      have := stxn xl
      contradiction
    /-
      rcases yst with ⟨y1,y2⟩ | ⟨y3,y4⟩
      · contradiction 
      · contradiction
      -/
    · constructor; repeat assumption

/-
    --could have used constructor but had issues

    #check HEq Knight Knave
    #check Eq Knight Knave
--    rw [Xor'] at h1
 --   rw [Xor'] at h2

  -- x says y is a knight
  -- y says that x and y are of different type
  --rules of the game, i.e knights tell the truth but knaves lie
    cases h1
    cases h2
    --unfold Xor' at *
    have contr := sty (stx h_1.left )
    cases contr
    have h_4 := mem_inter h_2.left h_3.right
    rw [h] at h_4
    contradiction
    -- replace with Function.mt , Function.mtr
    have heee := contrapositive stx
    have h_4 := mem_inter h_1.left h_3.left
    rw [h] at h_4
    contradiction

    have contr := styn h_2.left
    push_neg at contr
    have contr1 := contr.left h_1.left
    have contr2 := h_2.left
    contradiction

    exact And.intro h_1.left (stxn h_1.left )
-/
  }



example --(preamble := unfold Xor' at *)
  --sets
  (Knight : Set K ) (Knave : Set K)
  (h : Knight ∩ Knave = ∅ ) (h1 : Xor' (x ∈ Knight) (x ∈ Knave) ) (h2: Xor' (y ∈ Knight)  (y ∈ Knave) )

  -- x says y is a knight
  -- y says that x and y are of different type
  --rules of the game, i.e knights tell the truth but knaves lie
  (stx : x ∈ Knight → y ∈ Knight) (sty: y ∈ Knight → (x ∈ Knight ∧ y ∈ Knave) ∨ (x ∈ Knave ∧ y ∈ Knight) )
  (stxn : x ∈ Knave →  y ∈ Knave) (styn: y ∈ Knave → ¬ ( (x ∈ Knight ∧ y ∈ Knave) ∨ (x ∈ Knave ∧ y ∈ Knight) ) )
  : x ∈ Knave ∧ y ∈ Knave := by
  rw [XorToOr x h] at h1
  rw [XorToOr y h] at h2
  #check IfToIff
  have : x ∉ Knight → y ∉ Knight := by 
    intro h'
    have := NotKnight_Knave h'
    exact Knave_NotKnight h (stxn (NotKnight_Knave  h'))
  have := IfToIff stx stxn

Conclusion "This last message appears if the level is solved."

/-asdf -/


NewTactic push_neg 
