import Game.Metadata

World "KnightsAndKnavesLemmas" 
Level 6

Title "`notinright_inleft`" 

Introduction 
"
This lemma applies to any two finite sets `left`,`right` given that `A` is in either in `left` or in `right`.

Remember notright_left from logic world. You can go back if you wish before proceeding with this level: link to prev level.

Truth table:
$
\\begin{array}{|c c|c|} 
\\hline
P  & P ∨ False \\\\
\\hline
T  & T \\\\
F  & F \\\\
\\hline
\\end{array}
$

Notice that `P`, `P ∨ False` always have the same truth value.

In this level, we know:
```
A ∈ left ∨ A ∈ right
A ∉ right
```
In other words, we have that `P ∨ False` is true. So we must have `P`.

Another way to express this is that you have two possibilities one of which(or both) is supposed to be true, and you know its definitely not the second option. All is left is the first option. 

Its either 'this' or 'that'. If its not 'that' then its definitely 'this'.


-- let the user do the simplification manually... then in the conclusion introduce `simp`.
"

#check or_false_iff

#check or_iff_not_imp_left
#check or_iff_not_imp_right
Statement notinright_inleft
  {A : K}
  {left : Finset K} {right : Finset K}
  {LeftorRight : A ∈ left ∨ A ∈ right}
(h' : A ∉ right) : A ∈ left := by
  --rw [or_false_iff] at LeftorRight
  --simp only [h',or_false_iff] at LeftorRight

  -------------------

  exact notright_left LeftorRight h'

Conclusion 
"
"

NewTheorem notright_left
