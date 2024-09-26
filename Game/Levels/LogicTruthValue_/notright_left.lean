example  {P Q : Prop} (Or : P ∨ Q)(notleft : ¬Q) : P := by 
  cases Or
  assumption
  contradiction

