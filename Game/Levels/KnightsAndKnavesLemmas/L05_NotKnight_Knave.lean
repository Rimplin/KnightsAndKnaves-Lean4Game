import Game.Metadata


World "KnightsAndKnavesLemmas"
Level 5

Title ""

Introduction 
"
"

Statement NotKnight_Knave
  --sets
  {Knight : Set K} {Knave : Set K}
{h : Knight ∩ Knave = ∅ }
{h1 : Xor' (A ∈ Knight) (A ∈ Knave) }
(h' : ¬ (A ∈ Knight) )
: A ∈ Knave  := by

  {
    unfold Xor' at h1
    cases h1 
    exfalso
    exact h' h_1.left
    exact h_1.left
  }



--#check Knave_NotKnight
#check NotKnight_Knave


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


/- Use these commands to add items to the game's inventory. -/



NewTactic exfalso
 NewTheorem NotKnight_Knave
-- NewDefinition Nat Add Eq

