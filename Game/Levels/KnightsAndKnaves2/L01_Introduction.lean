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
#check of_eq_true
#check of_eq_false
#check eq_true
#check eq_false
-- develop tactic if x in knight then x not in knave
/-
standard notation:
x ∈ Knight as xKnight
x ∉ Knight as xnKnight
-/
#check true_implies
Statement
  --sets
  (Knight : Set K ) (Knave : Set K)
  (h : Knight ∩ Knave = ∅ ) (h1 : Xor' (x ∈ Knight) (x ∈ Knave) ) (h2: Xor' (y ∈ Knight)  (y ∈ Knave) )

/- conventions
for implications, a ' would mean the conclusion of it
for x ∈ stateemnts, the prime would mean the truth version
-/
  -- x says y is a knight
  -- y says that x and y are of different type
  --rules of the game, i.e knights tell the truth but knaves lie
  -- maybe do Knights and Knaves thing as inductive type...
  /-
  inhabitant
  | Knight
  | Knave
  -/
  (stx : x ∈ Knight → y ∈ Knight) (sty: y ∈ Knight → (x ∈ Knight ∧ y ∈ Knave) ∨ (x ∈ Knave ∧ y ∈ Knight) )
  (stxn : x ∈ Knave →  y ∈ Knave) (styn: y ∈ Knave → ¬ ( (x ∈ Knight ∧ y ∈ Knave) ∨ (x ∈ Knave ∧ y ∈ Knight) ) )
  : x ∈ Knave ∧ y ∈ Knave := by
  {
    unfold Xor' at *
    rcases h1 with ⟨xKnight,xnKnave⟩|⟨xKnave,xnKnight⟩  
    /-
    case inl.intro => sorry
    case inr.intro => sorry
    -/
    
    · -- xKnight, conclude 
      have yKnight := stx xKnight
      -- sequence from y being a knight, concluding that y is not a knave. maybe this should be its own level or something. or maybe a different way of expressing the fact that anything is a one of knight or knave should replace that...
      rw [eq_true yKnight] at h2
      simp at h2
      --clear stx, can't really know if we need it or not... a bit more complicated than expected.... what if can't conclude anything from it then something reduce to the point we can but wouldn't that mean a contradiction
      obtain sty' := sty yKnight
      --clear sty
      -- stxn , antecedent is false, nothing to conclude
      --clear stxn
      -- y is a knight so not a knave, styn nothing to conclude
      --clear styn
      obtain xKnight' := eq_true xKnight
      obtain xnKnave' := eq_false xnKnave
      simp [xKnight',xnKnave'] at sty'
      obtain yKnave' := eq_true sty'
      simp [*] 
      simp [yKnave'] at styn
      rw [xKnight'] at styn
      simp at *
      

      /-
      rcases h2 with ⟨yKnight,ynKnave⟩|⟨yKnave,ynKnight⟩    
      · obtain yKnight := eq_true yKnight
        obtain ynKnave := eq_false ynKnave
        simp [*]
        simp only [yKnight,ynKnave] at sty
        rw [true_implies] at sty
        assumption

      /-
        have := sty yKnight
        contradiction
        -/
      · simp [*]
        -- this is trivial if i already obtained all the information from the cases of 'x' which i didn't, this should always be done regardless to enforce a rigid structure of reasoning.
      -- some sort of boolean reduction, which is taught during logic world truth value perspectives.
      --simp only [eq_true,eq_false] at xKnight
     -/ 
    · have := stxn xKnave
      constructor ; repeat assumption
      
  }
