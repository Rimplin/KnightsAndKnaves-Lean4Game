import Game.Metadata

World "KnightsAndKnavesLemmas" 
Level 8

Title "`notright_left`" 

Introduction
"
In this level, we have `P ∨ Q` which means that `P` is true or `Q` is true. Since we also know `¬Q` i.e `Q` is not true, the only option left is `P` being true.

We will first start by transforming `P ∨ Q` into `P ∨ False` using `¬Q`.

`¬Q` means that `Q` is False i.e `Q = False`.
We have the following theorem:
```
eq_false (h : ¬p) : p = False
```

Use `have` and `eq_false` to get `Q = False`.

"

#check or_false_iff
#check or_iff_not_imp_left
#check or_iff_not_imp_right
#check notright_left
Statement notright_left {P Q : Prop} (Or : P ∨ Q) (notright : ¬Q) (hPF : P ∨ False → P) : P := by
{
  have := eq_false notright
  Hint "Replace `Q` in `Or` with `False`"
  rw [this] at Or
  Hint "
  Since `P ∨ False` is true, then either `P` is true or `False` is true. Therefore, `P` must be true.

  Use the implication `hPF` to conclude `P` andclose the goal.

  "
  exact hPF Or
}
/-

```
or_false_iff (p : Prop) : p ∨ False ↔ p
```

  `P` and `P ∨ False` have the same truth value. We know `P ∨ False` is true, therefore `P` is true.

-/
#check or_false_iff

Conclusion 
"
"

NewTheorem notright_left eq_false
NewTactic simp
