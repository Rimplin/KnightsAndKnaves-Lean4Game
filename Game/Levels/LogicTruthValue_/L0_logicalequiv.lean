import Game.Metadata


World "LogicTruthValue_" 
Level 

Title "" 

#check iff_iff_implies_and_implies
Introduction 
"
We define the logical connective `↔` as:
`p ↔ q` means `(p → q) ∧ (q → p)` which you know how to deal with.

Extracing each implication,
```
h : p ↔ q
h.mp : p → q
h.mpr : q → p
```
`h.mp` is the forward direction and `h.mpr` is the backward direction.

What does this connective mean:
truth table

this means `p`,`q` have the same truth value. Either they are both true or they are both false. Therefore, `p`,`q` can be used interchangeably. You can think of `p ↔ q` as `p = q` and use `rw` in the same way you would use it with an actual `=` in the expression.

Do `rw` using `QiffP` or extract the forward direction of `PiffQ` and combine it with `hP` to prove `Q`.
"

Statement {P Q : Prop} (hP : P) (PiffQ : P ↔ Q) (QiffP : Q ↔ P)
  : Q  := by

  {
    exact PiffQ.mp hP
  }

Conclusion 
"
Here are both solutions:
```
exact PiffQ.mp hP
```

```
rw [QiffP]
exact hP
```

Try the one which you didn't choose first.

"
