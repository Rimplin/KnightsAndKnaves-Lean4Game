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

  -- x says y is a knight
  -- y says that x and y are of different type
  --rules of the game, i.e knights tell the truth but knaves lie
  (stx : x ∈ Knight → y ∈ Knight) (sty: y ∈ Knight → (x ∈ Knight ∧ y ∈ Knave) ∨ (x ∈ Knave ∧ y ∈ Knight) )
  (stxn : x ∈ Knave →  y ∈ Knave) (styn: y ∈ Knave → ¬ ( (x ∈ Knight ∧ y ∈ Knave) ∨ (x ∈ Knave ∧ y ∈ Knight) ) )
  : x ∈ Knave ∧ y ∈ Knave := by
  {
    rcases h1 with ⟨xKnight,xnKnave⟩|⟨xKnave,xnKnight⟩  
    · obtain xKnight := eq_true xKnight
      obtain xnKnave := eq_false xnKnave
      simp [xKnight,xnKnave] at sty
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
      
    · sorry
  }
