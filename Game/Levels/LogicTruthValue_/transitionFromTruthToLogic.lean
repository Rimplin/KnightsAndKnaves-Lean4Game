import Game.Metadata
-- make an entire world about propositions as types, but where would this go??? well, no need because it would be explained plainly and intuitively.
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
