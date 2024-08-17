import Game.Metadata


World ""
Level 

Title ""

Introduction 
"
"

example
  --sets
  (Knight : Set K ) (Knave : Set K)
(h : Knight ∩ Knave = ∅ )
(h1 : Xor' (x ∈ Knight) (x ∈ Knave) ) 
(h2: Xor' (y ∈ Knight)  (y ∈ Knave) )
(stx : x ∈ Knight → x ∈ Knave ∧ y ∈ Knight)
(stxn : x ∈ Knave → ¬ (x ∈ Knave ∧ y ∈ Knight)) : x ∈ Knave ∧ y ∈ Knave := by{
  sorry
  }





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/



-- NewTactic rw rfl
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq


--open Set
#check Set.mem_of_mem_inter_left

/-
example
  --sets
  (Knight : Set K ) (Knave : Set K)
(h : Knight ∩ Knave = ∅ )
(h1 : Xor' (x ∈ Knight) (x ∈ Knave) ) 
(h2: Xor' (y ∈ Knight)  (y ∈ Knave) )
(stx : x ∈ Knight → x ∈ Knave ∧ y ∈ Knight)
(stxn : x ∈ Knave → ¬ (x ∈ Knave ∧ y ∈ Knight)) : x ∈ Knave ∧ y ∈ Knave := by{
  cases h1 with
  | inl hxknight => 
  have := stx hxknight.left 
  have := absurd (mem_inter_of_mem hxKnight h) (ne_empty_of_mem hxyKnight.2)

  | inr hxknave => sorry
  }
-/
example {x y : K}   (Knight : Set K ) (Knave : Set K) (h : Knight ∩ Knave = ∅ ) (h1 : Xor' (x ∈ Knight) (x ∈ Knave) ) (h2: Xor' (y ∈ Knight)  (y ∈ Knave) ) (stx : x ∈ Knight → x ∈ Knave ∧ y ∈ Knight) (stxn : x ∈ Knave → ¬ (x ∈ Knave ∧ y ∈ Knight) ): x ∈ Knave ∧ y ∈ Knave :=
by
  cases h1 with
  | inl hxKnight =>
 
    have hxyKnight : x ∈ Knave ∧ y ∈ Knight := stx hxKnight.left

    have : x ∈ Knight ∩ Knave := ⟨hxKnight.left, hxyKnight.1⟩
    rw [h] at this
    contradiction
  | inr hxKnave =>

    have hxKnight : ¬ (x ∈ Knave ∧ y ∈ Knight) := stxn hxKnave.left

    cases h2 with
    | inl hyKnight =>
      exfalso
      exact hxKnight ⟨hxKnave.left,hyKnight.left⟩
      --contradiction
    | inr hyKnave =>
     
      exact ⟨hxKnave.left, hyKnave.left⟩
  
/-
variable {K : Type} {Knight Knave : Set K}
variable {x y : K}
variable (h : Knight ∩ Knave = ∅)
variable (h1 : ∀ x, Xor' (x ∈ Knight) (x ∈ Knave))
--variable (h2: ∀ y, Xor' x, x ∈ Knight →  (y ∈ Knight)  (y ∈ Knave))
variable (stx : ∀x ∈ Knave ∧ y ∈ Knight)
variable (stxn : ∀ x, x ∈ Knave → ¬ (x ∈ Knave ∧ y ∈ Knight))

example {x y : K} : x ∈ Knave ∧ y ∈ Knave :=
by
sorry



example : x ∈ Knave ∧ y ∈ Knave :=
by
cases h1 x with 
| inl hxknight=>

 
    have hxy := stx x hxknight.left

    have : y ∉ Knave := fun h => absurd (mem_inter_of_mem hxKnight h) (ne_empty_of_mem hxyKnight.2)


    contradiction
  | inr hxKnave => 

  have hxKnight:  ¬ (x ∈ Knave  ∧ y ∈ Knight ):=stxn x hxKnave

 have hyKnave := h2 y
cases hyKnave with


| inl hxknight=>
contradiction


| inr hyKnave=>
exact⟨hxKnave,hyKnave⟩
-/



limboo7
 — 
Today at 8:19 PM
example
  --sets
  (Knight : Set K ) (Knave : Set K)
(h : Knight ∩ Knave = ∅ )
(h1 : Xor' (x ∈ Knight) (x ∈ Knave) ) 
(h2: Xor' (y ∈ Knight)  (y ∈ Knave) )
(stx : x ∈ Knight → x ∈ Knave ∧ y ∈ Knight)
(stxn : x ∈ Knave → ¬ (x ∈ Knave ∧ y ∈ Knight)) : x ∈ Knave ∧ y ∈ Knave := by{
  sorry
  }
import Mathlib
variable {K : Type} {Knight Knave : Set K}
variable (h : Knight ∩ Knave = ∅)
variable (h1 : ∀ x, Xor' (x ∈ Knight) (x ∈ Knave))
variable (h2: ∀ y, Xor' (y ∈ Knight)  (y ∈ Knave))
variable (stx : ∀ x, x ∈ Knight → x ∈ Knave ∧ y ∈ Knight)
variable (stxn : ∀ x, x ∈ Knave → ¬ (x ∈ Knave ∧ y ∈ Knight))

example {x y : K} : x ∈ Knave ∧ y ∈ Knave :=
by
cases h1 x with 
| inl hxknight=>
Sleepy
 — 
Today at 8:21 PM
variable {x y : K}
limboo7
 — 
Today at 8:28 PM
import Mathlib
variable {K : Type} {Knight Knave : Set K}
variable {x y : K}
variable (h : Knight ∩ Knave = ∅)
variable (h1 : ∀ x, Xor' (x ∈ Knight) (x ∈ Knave))
variable (h2: ∀ y, Xor' (y ∈ Knight)  (y ∈ Knave))
variable (stx : ∀ x, x ∈ Knight → x ∈ Knave ∧ y ∈ Knight)
variable (stxn : ∀ x, x ∈ Knave → ¬ (x ∈ Knave ∧ y ∈ Knight))

example {x y : K} : x ∈ Knave ∧ y ∈ Knave :=
by
cases h1 x with 
| inl hxknight=>

 
    have hxyKnight : x ∈ Knave ∧ y ∈ Knight := stx x hxKnight

    have : y ∉ Knave := fun h => absurd (mem_inter_of_mem hxKnight h) (ne_empty_of_mem hxyKnight.2)


    contradiction
  | inr hxKnave => 

  have hxKnight:  ¬ (x ∈ Knave  ∧ y ∈ Knight ):=stxn x hxKnave

 have hyKnave := h2 y
cases hyKnave with


| inl hxknight=>
contradiction


| inr hyKnave=>
exact⟨hxKnave,hyKnave⟩
limboo7
 — 
Today at 8:35 PM
example {x y : K} : x ∈ Knave ∧ y ∈ Knave :=
by
  cases h1 x with
  | inl hxKnight =>
 
    have hxyKnight : x ∈ Knave ∧ y ∈ Knight := stx x hxKnight

    have : x ∈ Knight ∩ Knave := ⟨hxKnight, hxyKnight.1⟩
    contradiction
  | inr hxKnave =>

    have hxKnight : ¬ (x ∈ Knave ∧ y ∈ Knight) := stxn x hxKnave

    cases h2 y with
    | inl hyKnight =>
    Knight).
      contradiction
    | inr hyKnave =>
     ]
      exact ⟨hxKnave, hyKnave⟩

      
