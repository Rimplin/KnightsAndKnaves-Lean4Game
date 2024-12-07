import Game.Metadata

example (forward: (P → Q))
  : (¬Q → ¬P) := by
  {
    intro nq
    intro np 
    apply nq 
    apply forward
    assumption
  }
