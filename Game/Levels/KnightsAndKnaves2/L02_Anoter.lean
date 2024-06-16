
-- solving it the prolog way
example 
  --sets
  (Knight : Set K ) (Knave : Set K) 
  --(uni : Knight ∪ Knave) 
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
 --  show_goals
   cases h1  

   cases h2

   --cases h2
   · have statement:= stx h_1.left 
     have cont : False := by tauto 
     contradiction
   · exact ⟨h_1.left, h_2.left⟩ 

   cases h2 
   have statement := stnx h_1.left 
   have cont : x ∈ Knave ∧ y ∈ Knight ∨ x ∈ Knave ∧ y ∈ Knave := by exact Or.inl (And.intro h_1.left h_2.left)
   have cont2 :  x ∈ Knight ∧ y ∈ Knave ∨ x ∈ Knave ∧ y ∈ Knight ∨ x ∈ Knave ∧ y ∈ Knave := Or.inr cont
   contradiction

   have statement := stnx h_1.left 
   have cont : (x ∈ Knight ∧ y ∈ Knave ∨ x ∈ Knave ∧ y ∈ Knight) ∨ x ∈ Knave ∧ y ∈ Knave := Or.inr (And.intro h_1.left h_2.left)
   rw [or_assoc] at cont
   --have := or_assoc.1 cont
   contradiction

  }

