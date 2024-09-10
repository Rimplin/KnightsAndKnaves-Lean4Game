import Game.Metadata
-- problem 28
variable (Knight : Set K) (Knave : Set K)

#check XorToOr
example
  --sets
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{h2: B ∈ Knight ∨ B ∈ Knave }
{stA : A ∈ Knight  ↔ ((A ∈ Knave) ∨ (B ∈ Knave)) }

-- use def???
--{atleastone : A ∈ Knave ∨ B ∈ Knave}
--{ stA' : A ∈ Knight ↔ atleastone}
  : A ∈ Knight ∧ B ∈ Knave := by
  {
  -- book way, more or less
    have AnKnave: A ∉ Knave := by 
      intro AKnave
      have AOrB : A ∈ Knave ∨ B ∈ Knave := by left ; exact AKnave

      -- first way
      --rw [not_iff_not.symm] at stA 
      --rw [NotKnight_KnaveIff h h1] at stA
      --have nAOrB := stA.mp AKnave
      --contradiction

      -- book way
      have AKnight := stA.mpr AOrB
      rw [Knight_NotKnaveIff h h1] at AKnight
      contradiction
     
   --cases h1
   --· sorry
   --· sorry
    have AKnight := NotKnave_Knight h h1 AnKnave 
    constructor
    · assumption
    · have AknOrB := stA.mp AKnight
      exact disjunctiveSyllogism AknOrB AnKnave 
  }







--variable {K : Type}
--variable {Knight Knave : Set K}
--
--inductive Xor'' (P Q : Prop) : Prop
--| introL (p : P) (np : ¬Q) 
--| introR (q : Q) (nq : ¬P) 
--
--example
--
--{h : Knight ∩ Knave = ∅ }
--{h1 : A ∈ Knight ∨ A ∈ Knave }
--{h2: B ∈ Knight ∨ B ∈ Knave }
--{stA : A ∈ Knight  ↔ ((A ∈ Knave) ∨ (B ∈ Knave)) }
--: A ∈ Knight ∧ B ∈ Knave :=by
--  cases h1
--  { -- Case A is a Knight
--    cases h2
--    { -- Case B is a Knight
--      have A_Knight : A ∈ Knight := h1.introL
--      have B_Knave : B ∈ Knave := h2.introR
--      exact ⟨A_Knight, B_Knave⟩
--    }
--    { -- Case B is a Knave
--      have A_Knight : A ∈ Knight := h1.introL
--      have B_Knave : B ∈ Knave := stA.1 A_Knight h2.introR
--      exact ⟨A_Knight, B_Knave⟩
--    }
--  }
--  { -- Case A is a Knave
--    cases h2
--    { -- Case B is a Knight
--      have A_Knave : A ∈ Knave := h1.introR
--      have B_Knight : B ∈ Knight := stA.2 A_Knave h2.introL
--      exact ⟨B_Knight, h2.introL⟩
--    }
--    { -- Case B is a Knave
--      have A_Knave : A ∈ Knave := h1.introR
--      have B_Knave : B ∈ Knave := h2.introR
--      exact ⟨stA.1 A_Knave h2.introR, B_Knave⟩
--    }
--  }
