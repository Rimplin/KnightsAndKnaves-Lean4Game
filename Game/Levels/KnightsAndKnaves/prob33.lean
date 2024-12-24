import Game.Metadata

World "KnightsAndKnaves"
Level 4

Title ""

Introduction
"
Suppose `A` says 'I am a knave, but B is not'.

If we assume `A ∈ Knight`, then we get `A ∈ Knave` which is a contradiction.

So `A ∉ Knight`.
"

Statement
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{h2: B ∈ Knight ∨ B ∈ Knave }
{stA : A ∈ Knight  ↔ (A ∈ Knave  ∧  B ∉ Knave) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave  ∧  B ∉ Knave) }
  :  A ∈ Knave ∧ B ∈ Knave:= by
  have AnKnight : A ∉ Knight := by
    intro AKnight 
    have ⟨AKnave,BnKnave⟩  := stA.mp AKnight
    have AnKnight := inright_notinleft h AKnave
    contradiction

  Hint "So, `A ∈ Knave`."
  have AKnave := notinleft_inright h1 AnKnight
  Hint "Since `A ∈ Knave`, `A ∉ Knave ∨ B ∈ Knave`"
  have := stAn.mp AKnave
  rw [not_and_or] at this
  Hint "Since `A ∉ Knave ∨ B ∈ Knave` and `A ∈ Knave` then `B ∈ Knave`."
  simp [AKnave] at this
  constructor
  repeat assumption

example {x y : K}   (Knight : Set K ) (Knave : Set K) (h : Knight ∩ Knave = ∅ ) (h1 : Xor' (x ∈ Knight) (x ∈ Knave) ) (h2: Xor' (y ∈ Knight)  (y ∈ Knave) ) (stx : x ∈ Knight → x ∈ Knave ∧ y ∈ Knight) (stxn : x ∈ Knave → ¬ (x ∈ Knave ∧ y ∈ Knight) ): x ∈ Knave ∧ y ∈ Knave :=
by
  cases h1 with
  | inl hxKnight =>
 
    have hxyKnight : x ∈ Knave ∧ y ∈ Knight := stx hxKnight.left

    have : x ∈ Knight ∩ Knave := ⟨hxKnight.left, hxyKnight.1⟩
    rw [h] at this
    contradiction
  | inr hxKnave =>

    have hxKnight : ¬ (x ∈ Knave ∧ y ∈ Knight) := stxn hxKnave.left

    cases h2 with
    | inl hyKnight =>
      exfalso
      exact hxKnight ⟨hxKnave.left,hyKnight.left⟩
    | inr hyKnave =>

      exact ⟨hxKnave.left, hyKnave.left⟩

Conclusion 
"
"

NewTactic push_neg
NewTheorem not_and_or
