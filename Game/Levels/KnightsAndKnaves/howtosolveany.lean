import Game.Metadata

example
  {inst : DecidableEq K}
  (Knight : Finset K ) (Knave : Finset K)
(h : Knight ∩ Knave = ∅ )
(h1 : A ∈ Knight ∨ A ∈ Knave ) 
(h2: B ∈ Knight ∨ B ∈ Knave )
(h3: C ∈ Knight ∨ C ∈ Knave )
(stB : B ∈ Knight ↔ ( A ∈ Knight ↔ A ∈ Knave  ) )
(stC : C ∈ Knight ↔ B ∈ Knave)
 : B ∈ Knave ∧ C ∈ Knight := by{
-- solving it the prolog way
  cases h1
  · cases h2
    · cases h3
      · tauto
      · have := inleft_notinright h h_1 
        tauto
    · cases h3 
      · tauto
      · tauto

  · cases h2
    · cases h3
      · tauto
      · have := inright_notinleft h h_1 
        tauto

    · cases h3 
      · tauto
      · tauto
}

example 
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

   · cases h2

     --cases h2
     · have statement:= stx h_1.left 
       tauto
     · tauto
      --exact ⟨h_1.left, h_2.left⟩ 

   · cases h2 
     · have statement := stnx h_1.left 
       tauto
       --have cont : x ∈ Knave ∧ y ∈ Knight ∨ x ∈ Knave ∧ y ∈ Knave := by exact Or.inl (And.intro h_1.left h_2.left)
       --have cont2 :  x ∈ Knight ∧ y ∈ Knave ∨ x ∈ Knave ∧ y ∈ Knight ∨ x ∈ Knave ∧ y ∈ Knave := Or.inr cont
       --contradiction

     · 
       have statement := stnx h_1.left 
       tauto
       --have cont : (x ∈ Knight ∧ y ∈ Knave ∨ x ∈ Knave ∧ y ∈ Knight) ∨ x ∈ Knave ∧ y ∈ Knave := Or.inr (And.intro h_1.left h_2.left)
       --rw [or_assoc] at cont
       ----have := or_assoc.1 cont
       --contradiction
  }
