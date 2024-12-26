import Game.Metadata

World "KnightsAndKnaves"
Level 4

Title ""

Introduction
"
Suppose `A` says 'I am a knave, but `B` is not' i.e `A ∈ Knave ∧ B ∉ Knave`.

For `stAn` we would have `A ∈ Knave ↔ ¬(A ∈ Knave ∧ B ∉ Knave)` which is equivalent to:
```
stAn : A ∈ Knave ↔ A ∉ Knave ∨ B ∈ Knave
```
"

Statement
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{h2: B ∈ Knight ∨ B ∈ Knave }
{stA : A ∈ Knight  ↔ (A ∈ Knave  ∧  B ∉ Knave) }
{stAn : A ∈ Knave ↔ A ∉  Knave  ∨  B ∈ Knave }
  :  A ∈ Knave ∧ B ∈ Knave:= by
  Template
  have AnKnight : A ∉ Knight := by
    Hole
    Hint 
    "
    Assuming `AKnight : A ∈ Knight`:
    - Prove `AKnBnKn : A ∈ Knave ∧ B ∉ Knave` using `AKnight`, `stA`
    - Prove `False` using `disjoint` , `AKnBnKn.left : A ∈ Knave` , `AKnight : A ∈ Knight`.
    "
    intro AKnight
    have AKnBnKn  := stA.mp AKnight
    exact disjoint h AKnight AKnBnKn.left

  Hole
  Hint "Prove `AKnave : A ∈ Knave` using `notleft_right` , `{AnKnight} : A ∉ Knight`"
  have AKnave := notleft_right h1 AnKnight
  Hint "Prove `AnKnBKn : A ∉ Knave ∨ B ∈ Knave` using `{AKnave} : A ∈ Knave` ,`stAn` "
  have AnKnBKn := stAn.mp AKnave
  Hint "Prove `BKnave : B ∈ Knave` using  `A ∉ Knave ∨ B ∈ Knave` and `{AKnave} : A ∈ Knave`. Use `simp` here. "
  simp [AKnave] at AnKnBKn
  exact And.intro AKnave AnKnBKn

Conclusion
"
"
