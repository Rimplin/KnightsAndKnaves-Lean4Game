import Game.Metadata

Introduction
"
This principle asserts that if you have contradictory assumptions then you can prove anything.
Example of contradictory assumptions:
```
h: P
nh: ¬P
```

Why is this principle valid? Well, this is what you will have to prove in this level. For your convenience, the contradiction tactic will be unlocked after this level so you don't have to do the same steps when there are contradictory assumptions.

False.elim eliminates false and produces an object of any type you want!!!
False implies anything.

$\\displaystyle {\\frac {P\\lor Q,\\neg P}{\\therefore Q}}$

"

variable {P Q:Prop} 
example (h : P) (nh : ¬P)
  : Q := by

  {
    have helper : P ∨ Q := Or.inl h
    exact notleft_right helper nh
  }

Conclusion
"
We have proven that `P ∧ ¬P → Q` for any proposition `Q`. since `P ∧ ¬P` is always false, then the implication proved becomes `False → Q`.

From contradiction, anything follows.
There are more examples of contradictions like 
¬(P ∨ ¬P)

$
\\begin{array}{|c c|c|} 
\\hline
P & ¬P & P ∨ ¬P & ¬(P ∨ ¬P) \\\\
\\hline
T & F & T & F \\\\
F & T & T & F \\\\
\\hline
\\end{array}
$
"
