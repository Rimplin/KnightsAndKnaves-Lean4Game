import Game.Metadata

/-
def Knight (A: Prop) :Prop:=A 
def Knave (A:Prop):Prop:= ¬A 
def A_stat(A_knave B_not_knave:Prop):Prop:=A_knave  ∧  B_knave
def A_knave(A_knave B_knave:Prop) : Prop :=Knave (A_stat A_knave B_knave:Prop) def A_Knight(A_knave B_knave : Prop):Prop := Knight (A_stat A_knave B_knave)

example: ∃ A_knave B_knave : Prop, A_knave ∧ B_knave := begin 
Knight (A : Prop) : Prop
Knave (A : Prop) : Prop
A_stat (A_knave B_knave : Prop) : Prop
-/ 

example
  --sets
  {Knight : Set Inhabitant} {Knave : Set Inhabitant}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{h2: B ∈ Knight ∨ B ∈ Knave }
{stA : A ∈ Knight  ↔ (A ∈ Knave  ∧  B ∉ Knave) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave  ∧  B ∉ Knave) }
  :  A ∈ Knave ∧ B ∈ Knave:= by

  {
  rcases h1 with AKnight|AKnave
  · 
    have AKnBK:= stA.mp AKnight
    -- contradiction
    exfalso
    exact disjoint h AKnight AKnBK.left
  · have := stAn.mp AKnave
    rw [not_and_or] at this
    cases this
    contradiction
    push_neg at h_1
    constructor
    assumption ; assumption
    --have AKnBK:= stA.mp AKnight

  }





Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/



-- NewTactic rw rfl
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

