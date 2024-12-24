import Game.Metadata
World "KnightsAndKnavesLemmas" 
Level 6

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


In this level, we have `P ∨ Q` which means that `P` is true or `Q` is true. Since we also know `¬P` i.e `P` is not true, the only option left is `Q` being true.

We will first start by transforming `P ∨ Q` into `False ∨ Q` using `¬P`.

`¬P` means that `P` is False i.e `P = False`.
We have the following theorem:
```
eq_false (h : ¬p) : p = False
```

Use `have` and `eq_false` to get `P = False`.
"

Statement notleft_right {P Q : Prop} (Or : P ∨ Q) (notleft : ¬P) ( hFQ: False ∨ Q → Q) : Q := by
{
  have := eq_false notleft 
  Hint "Replace `P` in `Or` with `False`"
  rw [this] at Or
  Hint "   Since `False ∨ Q` is true, then either `Q` is true or `False` is true. Therefore, `Q` must be true.

  Use the implication `hFQ` to conclude `P` andclose the goal.
"
  rw [false_or] at Or
  assumption
}

Conclusion 
"
Instead of doing it manually, you can instead use `simp` tactic. 

The `simp` tactic uses lemmas and hypotheses to simplify the main goal target or some assumption.

`simp [notright] at Or` does the job. It simplifies `Or` using `notright` and various theorems called 'simp lemmas' some of which are `eq_false`, `or_false_iff`.

`simp` will simplify `Or` with the theorems you gave, in this case `notright : ¬Q`. The resulting simplified expression would be `Or : P`.
"

NewTheorem notleft_right
