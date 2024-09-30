import Game.Metadata
-- problem 28
variable (Knight : Finset K) (Knave : Finset K)

#check XorToOr
example
  {inst : DecidableEq K}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{h2: B ∈ Knight ∨ B ∈ Knave }
{stA : A ∈ Knight  ↔ ((A ∈ Knave) ∨ (B ∈ Knave)) }
  : A ∈ Knight ∧ B ∈ Knave := by
  {
  -- book way, can't be further optimized
    have AnKnave: A ∉ Knave := by 
      intro AKnave
      have AOrB : A ∈ Knave ∨ B ∈ Knave := by left ; exact AKnave 
      have AKnight := stA.mpr AOrB
      exact disjoint h AKnight AKnave

    have AKnight := notinright_inleft h1 AnKnave 
    constructor
    · assumption
    · have AknOrB := stA.mp AKnight
      exact notleft_right AknOrB AnKnave 
  }

