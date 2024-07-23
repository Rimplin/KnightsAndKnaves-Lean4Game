import Game.Metadata


World "Logic" 
Level 7

Title "Contrapositive" 

Introduction 
"
More practice on implication and negation
"
variable { P Q : Prop }
/-
Statement  contrapositive
  : (P → Q) ↔ (¬Q → ¬P) := by

  {
   constructor

   intro h 
   intro nq

   intro p 
   exact nq (h p)  
   
   intro h
   have : P → Q:= by tauto

   exact this

   --intro p 
    
  }
-/
/--testssstsgasdfa-/
TheoremDoc contrapositive as "contrapositive" in "logic"
Statement (forward: (P → Q))
  : (¬Q → ¬P) := by

  {
    intro nq
    intro p
    Hint "To obtain `False`, we need `Q`, and to obtain `Q` we need `P` which we have. Construct the appropriate expression to obtain `False`"
    exact nq (forward p)
   --intro h 
   --intro nq

   --intro p 
   --exact nq (h p)  
}

Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

NewTactic tauto
NewTheorem contrapositive
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

