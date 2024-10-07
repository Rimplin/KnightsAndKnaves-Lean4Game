import Game.Metadata

World "KnightsAndKnavesLemmas"
Level 9

Title ""

Introduction 
"
Similar to the previous level
"

Statement 
  {inst : DecidableEq K}
  {Knight : Finset K} {Knave : Finset K}
{h : Knight ∩ Knave = ∅ }
{Or : A ∈ Knight ∨ A ∈ Knave}
(h' : ¬ (A ∈ Knight) )
: A ∈ Knave  := by

  {
    exact notinleft_inright Or h'
  }

Conclusion 
"
Let's recap what we have proven in the last four levels.

Given the following proof state:
```
(Knight : Set K ) (Knave : Set K)
(h : Knight ∩ Knave = ∅ )
(h'' : ∀ (x: K), x ∈ Knight ∨ x ∈ Knave)
```


We can conclude the following implications:
A ∈ Knight → A ∉ Knave  
A ∉ Knave → A ∈ Knight
which can be combined into: A ∈ Knight ↔ A ∉ Knave
Similarly for the other two levels, we can conclude A ∉ Knight ↔ A ∈ Knave

These two theorems will be very useful in the following world.

------------------------

We have proven:
```
(Knight : Set K) (Knave : Set K)
(h : Knight ∩ Knave = ∅ )
(h' : A ∈ Knight)
  : A ∉ Knave 



(Knight : Set K ) (Knave : Set K)
(h : Knight ∩ Knave = ∅ )
(h' : ¬ (B ∈ Knave))
(h'' : ∀ (x: K), x ∈ Knight ∨ x ∈ Knave)
  :  B ∈ Knight := by
```
"

NewTactic exfalso
