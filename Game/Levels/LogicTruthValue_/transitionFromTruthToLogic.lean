import Game.Metadata
example (hP : P=True) (hQ : Q=True) 
  : (P ∨ Q) = True := by {
  apply eq_true 
  obtain hP' := of_eq_true hP ; clear hP
  obtain hQ' := of_eq_true hQ ; clear hQ
  left
  assumption
}
#check of_eq_true
#check eq_true
