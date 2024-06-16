import Game.Metadata

open Set

variable {K : Type}

World "KnightsAndKnaves"
Level 2

Title "lev 2"

Introduction "Hi"

--Raymond Smullyan, what is the name of this book, problem 28
Statement
  --sets
  (Knight : Set K ) (Knave : Set K)
  (h : Knight ∩ Knave = ∅ )
  (h1 : Xor' (x ∈ Knight) (x ∈ Knave) ) 
  (h2: Xor' (y ∈ Knight)  (y ∈ Knave) )
  -- theres x and y, x says at least one of us is a knave
  --rules of the game, i.e knights tell the truth but knaves lie
  (stx : x ∈ Knight → (x ∈ Knight ∧  y ∈ Knave)
                    ∨ (x ∈ Knave ∧ y ∈ Knight)
                    ∨ (x ∈ Knave ∧ y ∈ Knave)  )
  (stnx : x ∈ Knave → ¬ ( (x ∈ Knight ∧  y ∈ Knave)
                    ∨ (x ∈ Knave ∧ y ∈ Knight)
                    ∨ (x ∈ Knave ∧ y ∈ Knave) ) )
--goal
  : x ∈ Knight ∧ y ∈ Knave:= by
  {

   --rw [Xor'] at h1
   --rw [Xor'] at h2
   --exact h1
   --rw [Eq.rfl h1 ( (x ∈ Knight ∧ x ∉ Knave)  ∨ (x ∈ Knave ∧ x ∉ Knight ) )] at h1
   --cases h1
   --cases h2

   -- no need to take two cases, explain to the user why!!!!
   cases h1 
   --cases h2
   
   have contr :=  stx h_1.left 
   rcases contr    

   exact h_2

   cases h_2 
   have contr2 := mem_inter h_1.left h_3.left 
   rw [h] at contr2
   contradiction


   have contr2 := mem_inter h_1.left h_3.left 
   rw [h] at contr2
   contradiction

   have contr := stnx h_1.left
   push_neg at contr
   have yK := contr.right.left h_1.left 
   have yk2 : y ∈ Knave := by {
     rw [Xor'] at h2
     cases h2 
     have contr2:= h_2.left
     contradiction

     exact h_2.left
   }
  
   have target := contr.right.right
   contrapose target
   push_neg
   push_neg at target

   have target2 : y ∈ Knave → x ∉ Knight := by {
     intro h 
     -- writing an implication as a disjunction...., this is tough
   }
  }



example (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq


Conclusion "."

/- Use these commands to add items to the game's inventory. -/


-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq



