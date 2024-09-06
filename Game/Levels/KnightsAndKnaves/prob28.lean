import Game.Metadata
-- problem 28
variable (Knight : Set K) (Knave : Set K)

example
  --sets
{h : Knight ∩ Knave = ∅ }
{h1 : Xor' (A ∈ Knight) (A ∈ Knave) }
{h2: Xor' (B ∈ Knight)  (B ∈ Knave) }
{stA : A ∈ Knight  ↔ ((A ∈ Knave) ∨ (B ∈ Knave)) }
  : A ∈ Knight ∧ B ∈ Knave := by
  {
    --#check Knave_NotKnight

    have this := h1
    unfold Xor' at h1
    cases h1 
    · have := stA.mp h_1.left
      cases this 
        -- having Xor and all that might get a rewrite so this would need to change
      · sorry--have := Knave_NotKnight h this h_2
        ----have := @Knave_NotKnight K A Knight Knave h this h_2
        --exfalso 
        --exact this h_1.left

      · sorry
    · sorry
  }



