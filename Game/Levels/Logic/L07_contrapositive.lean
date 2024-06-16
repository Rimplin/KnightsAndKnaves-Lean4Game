import Game.Metadata


World "Logic" 
Level 6

Title "Contrapositive" 

Introduction 
"

"
variable { P Q : Prop }
Statement  
  : (P → Q) ↔ (¬Q → ¬P) := by

  {
   constructor

   intro h 
   intro nq

   intro p 
   exact nq (h p)  
   
   intro h
   have : P → Q:= by tauto

   exact h

   --intro p 
    
  }





Conclusion 
"
".

/- Use these commands to add items to the game's inventory. -/

--NewTactic rw rfl
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

