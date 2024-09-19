import Game.Metadata

-- alex
example 

  (Knight : Set K) (Knave : Set K)

  (h : Knight ∩ Knave = ∅) 

  (h1 : Xor' (x ∈ Knight) (x ∈ Knave)) 

  (h2: Xor' (y ∈ Knight) (y ∈ Knave)) 

  (stx : x ∈ Knight → y ∈ Knight) 

  (sty: y ∈ Knight → (x ∈ Knight ∧ y ∈ Knave) ∨ (x ∈ Knave ∧ y ∈ Knight)) 

  (stxn : x ∈ Knave → y ∈ Knave) 

  (styn: y ∈ Knave → ¬((x ∈ Knight ∧ y ∈ Knave) ∨ (x ∈ Knave ∧ y ∈ Knight))) 

  : x ∈ Knave ∧ y ∈ Knave := by

{



  rcases h1 with h_1|h_2

  {

 

    have h4 := stx h_1.left



    have h5 := sty h4

    rcases h5 with h_5|h_51

    { exfalso; sorry -- exact h h5.1 h5.2 

    }

    { exfalso; sorry -- exact h h5.2 h5.1 

    }

  }

  {



    have h5 := stxn h_2.left



    exact ⟨h_2.left, h5⟩

  }

}







example 

  (Knight : Set K) (Knave : Set K) 

  (h : Knight ∩ Knave = ∅)

  (h1 : Xor' (x ∈ Knight) (x ∈ Knave)) 

  (h2: Xor' (y ∈ Knight)  (y ∈ Knave)) 

  (stx : x ∈ Knight → (x ∈ Knight ∧  y ∈ Knave) ∨ (x ∈ Knave ∧ y ∈ Knight) ∨ (x ∈ Knave ∧ y ∈ Knave)) 

  (stnx : x ∈ Knave → ¬((x ∈ Knight ∧  y ∈ Knave) ∨ (x ∈ Knave ∧ y ∈ Knight) ∨ (x ∈ Knave ∧ y ∈ Knave))) 

  : x ∈ Knight ∧ y ∈ Knave := by

{



  rcases h1 with h_1|h_2

  {



  

    have h5 := stx h_1.left

    rcases h5 with h5_1|h5_2

    { exact h5_1 }

    { rcases h5_2 with h5_3|h5_4

      { exfalso; exact h_1.right h5_3.left }

      { exfalso; exact h_1.right h5_4.left } 

    }



  }



  {



    have h4 := stnx h_2.left

    

    rcases h2 with h2_1|h2_2

    {exfalso; exact h4 (Or.inr (Or.inl (⟨h_2.left,h2_1.left⟩)))}

    {exfalso; exact h4 (Or.inr (Or.inr (⟨h_2.left,h2_2.left⟩)))}

  }



}
