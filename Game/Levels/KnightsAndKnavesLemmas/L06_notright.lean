import Game.Metadata

World "KnightsAndKnavesLemmas" 
Level 6

Title "`notright_left`" 

Introduction
"
In this level, we have `P ∨ Q` which means that `P` is true or `Q` is true. Since we also know `¬Q` i.e `Q` is not true, the only option leftis `P` being true.

As a truth table:
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

This truth table is represented as the following theorem:
```
or_false_iff (p : Prop) : p ∨ False ↔ p
```

We will first start by transforming `P ∨ Q` into `P ∨ False` using `¬Q`.

`¬Q` means that `Q` is False i.e `Q = False`.
We have the following theorem:
```
eq_false {p : Prop} (h : ¬p) : p = False
```

Use `have` and `eq_false` to get `Q = False`.

"

#check or_false_iff
#check or_iff_not_imp_left
#check or_iff_not_imp_right
#check notright_left
Statement notright_left {P Q : Prop} (Or : P ∨ Q) (notright : ¬Q) : P := by
{
  have := eq_false notright
  Hint "Replace `Q` in `Or` with `False`"
  rw [this] at Or
  Hint "`P` and `P ∨ False` have the same truth value. We know `P ∨ False` is true, therefore `P` is true."
  rw [or_false_iff] at Or
  assumption
}

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

`simp [notright] at Or` does the job. It simplifies `Or` using `notright` and various theorems called 'simp lemmas' some of which are `eq_false`, `or_false_iff`.

`simp` will simplify `Or` with the theorems you gave, in this case `notright : ¬Q`. The resulting simplified expression would be `Or : P`.
"

NewTheorem notright_left
