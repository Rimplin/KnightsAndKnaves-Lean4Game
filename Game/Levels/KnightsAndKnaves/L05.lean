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
