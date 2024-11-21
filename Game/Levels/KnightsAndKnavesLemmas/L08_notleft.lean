import Game.Metadata
World "KnightsAndKnavesLemmas" 
Level 8

Title "`notleft_right`"

Introduction 
"
Truth table:
$
\\begin{array}{|c|c|} 
\\hline
P  & False ∨ P \\\\
\\hline
T  & T \\\\
F  & F \\\\
\\hline
\\end{array}
$
Notice that `P`, `False ∨ P` always have the same truth value.
"

Statement notleft_right {P Q : Prop} (Or : P ∨ Q) (notleft : ¬P) : Q := by
{
  have := eq_false notleft 
  rw [this] at Or
  rw [false_or] at Or
  assumption
}

Conclusion 
"
"

NewTheorem notleft_right
