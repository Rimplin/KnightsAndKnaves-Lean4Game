import Game.Metadata

World "KnightsAndKnavesLemmas" 
Level 6

Title "`notright_left`" 

Introduction
"
Truth table:
$
\\begin{array}{|c|c|} 
\\hline
P  & P ∨ False \\\\
\\hline
T  & T \\\\
F  & F \\\\
\\hline
\\end{array}
$

Notice that `P`, `P ∨ False` always have the same truth value.

Another way to express this is that you have two possibilities one of which(or both) is supposed to be true, and you know its definitely not the second option. All is left is the first option. 

Given the statement, its either 'this' or 'that'. If we know its not 'that' then its definitely 'this'.
"

#check or_false_iff

#check or_iff_not_imp_left
#check or_iff_not_imp_right
#check notright_left
Statement notright_left {P Q : Prop} (Or : P ∨ Q) (notright : ¬Q) : P := by
{
  have := eq_false notright
  rw [this] at Or
  rw [or_false] at Or
  assumption
}

--This lemma applies to any two finite sets `left`,`right` given that `A` is in either in `left` or in `right`.
--Statement notinright_inleft
--  {A : K}
--  {left : Finset K} {right : Finset K}
--  {LeftorRight : A ∈ left ∨ A ∈ right}
--(h' : A ∉ right) : A ∈ left := by
--  --rw [or_false_iff] at LeftorRight
--  --simp only [h',or_false_iff] at LeftorRight
--  -------------------
--  exact notright_left LeftorRight h'

Conclusion 
"
Instead of doing it manually, you can instead use `simp` tactic. 

The `simp` tactic uses lemmas and hypotheses to simplify the main goal target or some assumption.

`simp [notright] at Or` does the job. `simp` will simplify `Or` with the theorems you gave, in this case `notright : ¬Q`. The resulting simplified expression would be `Or : P`.
"

NewTheorem notright_left
