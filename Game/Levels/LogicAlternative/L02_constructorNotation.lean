import Game.Metadata


World "LogicAlternative" 
Level 2

Title "The `⟨⟩` notation" 

Introduction 
"
`⟨⟩` is another way to introduce `∧`.
Consider the following proof state:
```
h1 : P
h2 : Q
```
If your and introduction looks like the following:
```
And.intro h1 h2
```
then the equivalent `⟨⟩` syntax is:
```
⟨h1,h2⟩ 
```
Both notations produce/construct an object of type `P ∧ Q`
"

 
Statement (hP : P) (hQ : Q)
  : P ∧ Q  := by
{
  exact ⟨hP, hQ⟩ 
}



Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

--NewTactic 
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

