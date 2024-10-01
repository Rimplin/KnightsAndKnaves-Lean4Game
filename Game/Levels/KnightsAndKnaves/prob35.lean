import Game.Metadata
/-def Knight (A : Prop) : Prop := A 
 def Knave (A : Prop) : Prop := ¬A 
  def A_stat (B_knave C_knave : Prop) : Prop := (B_knave ↔ C_knave)
   def C_stat (A_knave B_knave : Prop) : Prop := (A_knave ↔ B_knave)
   def A_knave ( B_knave C_knave : Prop) : Prop := Knave (A_stat B_knave C_knave)
    def A_knight ( B_knave C_knave : Prop) : Prop := Knight (A_stat B_knave C_knave)
    def C_knave (A_knave B_knave C_knave : Prop) : Prop := Knave (C_stat A_knave B_knave) 
    def C_knight (A_knave B_knave C_knave : Prop) : Prop := Knight (C_stat A_knave B_knave)

    example : ∃ (A_knave B_knave C_knave : Prop), C_knight A_knave B_knave C_knave := begin
    Knight (A : Prop) : Prop
    Knave (A : Prop) : Prop
    A_stat (B_knave C_knave : Prop)
    C_stat(A_knave B_knave : Prop)

-/


example
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{Or : ∀(x : Inhabitant), x ∈ Knight ∨ x ∈ Knave}
{stA : A ∈ Knight  ↔ (B ∈ Knight ∧ C ∈ Knight ∨ B ∈ Knave ∧ C ∈ Knave) }
{stAn : A ∈ Knave ↔ ¬ (B ∈ Knight ∧ C ∈ Knight ∨ B ∈ Knave ∧ B ∈ Knave) }
-- this type doesn't work, it can't work, find a way to modify the problem
  : A ∈ Knight ∧ B ∈ Knight ∨ A ∈ Knave ∧ B ∈ Knave := by

  {
    rcases (Or A) with AKnight|AKnave
    · have BCsame := stA.mp AKnight
      rcases (Or C) with CKnight|CKnave 
      · have CnKnave := inleft_notinright h CKnight 
      -- A and B are same type
        simp [CKnight,CnKnave] at BCsame
        left
        constructor
        assumption
        assumption


      · -- A and B are of different type
        sorry
    · sorry
  }





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/



-- NewTactic rw rfl
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

