import Game.Metadata

#check propext
  -- axioms and computations, theorem proving in lean 4

inductive Solution (Knight : Finset Inhabitant) (Knave : Finset Inhabitant)
| submit (h : A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) : Solution (Knight) (Knave)
inductive Submit (P Q : Prop) 
| submit1 (h' : P)  (h'' : Q) (h : P ↔ Q) :Submit P Q
| submit2 (h' : P)  (h'' : ¬Q) (h : ¬(P ↔ Q)) :Submit P Q
| submit3 (h' : ¬P)  (h'' : Q)(h : ¬(P ↔ Q) ) :Submit P Q
| submit4 (h' : ¬P)  (h'' : ¬Q)(h : P ↔ Q) :Submit P Q
/-
1. type mismatch when assigning motive
     fun t => x✝ = t → Submit P Q
   has type
     P ∨ ¬P → Type : Type 1
   but is expected to have type
     P ∨ ¬P → Prop : Type
Statement (P Q : Prop)
  : Submit P Q := by

  {
    #check em
    cases em P
  }
-/

-- represent the truth table as a conjunction of implications, would need to resort to the truh value perspective and deal with those rules manually, maybe put it in an optional world.

example (P Q : Prop) :
(P ∧ Q → (P ↔ Q)) ∧ (P ∧ ¬Q → (¬ (P ↔ Q) ) ) 
∧ (¬P ∧ Q → (P ↔ Q)) ∧ (¬P ∧ ¬Q → (¬ (P ↔ Q) ) ) 
:= by 
  constructor
  · sorry
  · constructor
    · sorry
    · constructor
      sorry
      sorry
