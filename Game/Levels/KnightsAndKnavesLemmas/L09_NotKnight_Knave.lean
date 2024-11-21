import Game.Metadata

World "KnightsAndKnavesLemmas"
Level 9

Title "If you're not a knight, then the only option left is a knave."

Introduction 
"
You are either a knight or a knave. If you are not a knight, then the only option left is being a knave.

false_or

In this level, we know:
```
A ∈ Knight ∨ A ∈ Knave
A ∉ Knight
```
In our case, `P` is `A ∈ Knave`. Since we know `A ∉ Knight` then we can say that `A ∈ Knight = False`. Replacing this in the `∨` expression gives us `False ∨ A ∈ Knave`.

So we must have `A ∈ Knave`.
"

Statement
  {inst : DecidableEq K}
  {Knight : Finset K} {Knave : Finset K}
{h : Knight ∩ Knave = ∅ }
{Or : A ∈ Knight ∨ A ∈ Knave}
(h' : ¬ (A ∈ Knight) )
: A ∈ Knave  := by

  {
    exact notleft_right Or h'
  }

#check iff_iff_implies_and_implies
Conclusion 
"
Let's recap what we have proven.

Given the following proof state:
```
(Knight : Finset K ) (Knave : Finset K)
(h : Knight ∩ Knave = ∅ )
(h'' : A ∈ Knight ∨ A ∈ Knave)
```

We can conclude the following implications:
A ∈ Knight → A ∉ Knave (using `h`) 
A ∉ Knave → A ∈ Knight (using `h''`)
which can be combined into: A ∈ Knight ↔ A ∉ Knave.

Similarly for the other two levels, we can conclude A ∉ Knight ↔ A ∈ Knave

These two theorems will be very useful in the following world. They are now unlocked as the following:
```

```

------------------------

We have proven:
```
(Knight : Finset K) (Knave : Finset K)
(h : Knight ∩ Knave = ∅ )
(h' : A ∈ Knight)
  : A ∉ Knave 

(Knight : Finset K ) (Knave : Finset K)
(h : Knight ∩ Knave = ∅ )
(h' : ¬ (B ∈ Knave))
(h'' : B ∈ Knight ∨ B ∈ Knave)
  :  B ∈ Knight := by
```
"

NewTactic exfalso
