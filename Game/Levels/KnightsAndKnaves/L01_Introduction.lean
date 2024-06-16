import Game.Metadata

open Set

variable {K : Type}

World "KnightsAndKnaves"
Level 1

Title "Intro"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

-- develop tactic if x in knight then x not in knave
Statement
  --sets
  (Knight : Set K ) (Knave : Set K)
  (h : Knight ∩ Knave = ∅ ) (h1 : Xor' (x ∈ Knight) (x ∈ Knave) ) (h2: Xor' (y ∈ Knight)  (y ∈ Knave) )

  -- x says y is a knight
  -- y says that x and y are of different type
  --rules of the game, i.e knights tell the truth but knaves lie
  (stx : x ∈ Knight → y ∈ Knight) (sty: y ∈ Knight → (x ∈ Knight ∧ y ∈ Knave) ∨ (x ∈ Knave ∧ y ∈ Knight) )
  (stxn : x ∈ Knave →  y ∈ Knave) (styn: y ∈ Knave → ¬ ( (x ∈ Knight ∧ y ∈ Knave) ∨ (x ∈ Knave ∧ y ∈ Knight) ) )
  : x ∈ Knave ∧ y ∈ Knave := by
  {

    --could have used constructor but had issues

    cases h1
    cases h2

    have contr := sty (stx h_1.left )
    cases contr
    have h_4 := mem_inter h_2.left h_3.right
    rw [h] at h_4
    contradiction

    have h_4 := mem_inter h_1.left h_3.left
    rw [h] at h_4
    contradiction

    have contr := styn h_2.left
    push_neg at contr
    have contr1 := contr.left h_1.left
    have contr2 := h_2.left
    contradiction

    exact And.intro h_1.left (stxn h_1.left )

  }





  /-
  Hint "You can either start using `{h}` or `{g}`."
  Branch
    rw [g]
    Hint "You should use `{h}` now."
    rw [h]
  rw [h]
  Hint "You should use `{g}` now."
  rw [g]
-/
Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/


NewTactic cases push_neg 
--NewLemma Nat.add_comm Nat.add_assoc
--NewDefinition Nat Add Eq
