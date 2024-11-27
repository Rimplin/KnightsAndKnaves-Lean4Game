import Game.Metadata

World "KnightsAndKnaves" 
Level 3

Title "" 

Introduction 
"
A says 'I am a knave or B is a knave'.

Formally,
```
A ∈ Knave ↔ ¬ (A ∈ Knave ∨ B ∈ Knave)
```

If `A ∈ Knave` then we get `A ∉ Knave` which is a contradiction.

So, we can conclude that `A ∉ Knave`.
"

-- A says I am a knave or B is a knave
Statement 
{inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{all2 : ∀ (x : Inhabitant), x = A ∨ x = B}
{Or : ∀(x :Inhabitant), x ∈ Knight ∨ x ∈ Knave}
{stA : A ∈ Knight ↔ (A ∈ Knave ∨ B ∈ Knave) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∨ B ∈ Knave) }
: A ∈ Knight ∧ B ∈ Knave := by 
  -- explain this
  --push_neg at stAn 

  have AnKnave : A ∉ Knave := by 
    -- maybe have these astemplate
    intro AKnave
    have ABK := stAn.mp AKnave 
    -- teach this??
    -- prove A ∈ Knave ∨ B ∈ Knave
    exact ABK (by left ; assumption)

   -- exact ABK.left AKnave

  Hint
  "
Now that we know that `A` is not a knave, then `A` is a knight. 
  "
  have AKnight := notinright_inleft (Or A)  AnKnave

  Hint
  "
From this, we can conclude that `A ∈ Knave ∨ B ∈ Knave`. 
  "
  have AorBKn := stA.mp AKnight
  Hint
  "
Since `A ∉ Knave`, we can conclude `B ∈ Knave`.
  "
  simp [AnKnave] at AorBKn
  constructor
  repeat assumption

Conclusion 
"
"
