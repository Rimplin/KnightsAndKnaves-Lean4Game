import Game.Metadata

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

example (hP : P) (hQ : Q)
  : P ∧ Q  := by
{
  exact ⟨hP, hQ⟩ 
}
