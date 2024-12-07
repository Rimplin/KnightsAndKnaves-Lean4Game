import Game.Metadata

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
/-
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
-/

    /-
    intro nq
    intro p
    Hint "To obtain `False`, we need `Q`, and to obtain `Q` we need `P` which we have. Construct the appropriate expression to obtain `False`"
    exact nq (forward p)
    -/
   --intro h 
   --intro nq

   --intro p 
   --exact nq (h p)
