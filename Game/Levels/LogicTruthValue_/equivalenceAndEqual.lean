import Game.Metadata

#check iff_eq_eq.mp
-- ((P = Q) ↔ (P ↔ Q)) = True
example : ((P = Q) ↔ (P ↔ Q))  := by 
  rw [iff_def]

  constructor 
  · intro h
    rw [h] 

  · intro h
    rw [h]

#check eq_iff_iff
#check eq_self_iff_true
#check Eq

variable {P Q : Prop}
#check (P = Q) = P
#check (P ↔ Q) ↔ P
#check Iff
#print Iff
#check iff_def
