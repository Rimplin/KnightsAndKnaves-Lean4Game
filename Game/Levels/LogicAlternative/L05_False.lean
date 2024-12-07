import Game.Metadata

example (h : P) (hn : ¬ P)
  : False := by

  {
   apply hn 
   assumption
  }
