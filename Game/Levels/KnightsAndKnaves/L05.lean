import Game.Metadata



--variable (Inhabitant : Type)
--#check (Sum Inhabitant Inhabitant)
--variable (Knight Knave : Type)
--variable (A : Sum Knight Knave)
--inductive A where
--| Knight
--| Knave

-- Define a sum type that can be either an integer or a boolean
--inductive Inhabitant
--| int 
--| bool 
--variable (B : Knight)
--example : ( Sum.inl A ∈ Knight) := by
--  cases A 
  
--example : 2=2 := by sorry
--variable (Knight: Type) (Knave : Type)
--def Inhabitant := (Sum Knight Knave)
--#check Inhabitant
--example (A : Inhabitant Knight Knave) : 2=2  := sorry

/-
inductive Weekday where
  | sunday : Weekday
  | monday : Weekday
  | tuesday : Weekday
  | wednesday : Weekday
  | thursday : Weekday
  | friday : Weekday
  | saturday : Weekday
inductive Inhabitant where 
| Knight'
| Knave'

#check Inhabitant.Knave'
#check Inhabitant.Knight'
example (A : Inhabitant) : 2=2 :=  
  match A with 
  | Knight' => sorry
  | Knave' => sorry
-/
example (h : p ↔ q) (h' : q ↔ r) : p ↔ r := by 
  rw [h'] at h
  -- loss of information
  rw [h'] at h'
  assumption


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

open Set
#check not_mem_empty


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

