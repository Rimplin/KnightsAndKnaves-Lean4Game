import Game.Metadata


World "Logic" 
Level 2

Title "adsf" 

Introduction 
"
adf
"

Statement 
  : 2=2 := by

  {
    rfl
  }


-- try it 
open Classical

variable (p q r : Prop)

#check em
--#check 
example : (p → q ∨ r) → ((p → q) ∨ (p → r)) 
:=
  fun hpqr ↦ 
  @byContradiction ((p → q) ∨ (p → r))
  (fun hn ↦ _)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) 
:=
  fun hpqr ↦ 
  Or.elim (Classical.em p) 
  (fun hp ↦ Or.elim (hpqr hp) (fun hq ↦Or.inl (fun _ ↦ hq)) (fun hr ↦ Or.inr (fun _ ↦ hr)) ) (fun hnp ↦ Or.inl (fun hp ↦ absurd hp hnp))

-- constructor for implicaiton, this is to enable truth table interpretation...
theorem trueConsequent  (hq : q) : p → q :=
fun _ ↦ hq
theorem falseAntecedent  (hnp : ¬p) : p → q :=
fun hp ↦ absurd hp hnp
example (hp : p) (hq : q) : p → q :=  
  hp → hq

  have : p → q:= Implies p q

example (hp : p) (hq : q) : p → q := 
have :Implies p q := _
example : (p → q ∨ r) → ((p → q) ∨ (p → r)) 
:=
  fun hpqr ↦ 
    Or.elim (Classical.em p) (fun hp ↦ ) ()
example : ¬(p ∧ q) → ¬p ∨ ¬q := 
  fun hnpq ↦ 
    Or.elim (Classical.em ( ¬ (p∧q) ))
            ()
            ()
example : ¬(p ∧ q) → ¬p ∨ ¬q := 
  Or.elim (Classical.em p)
    (
    Or.elim (Classical.em q) 
            (fun hq ↦ fun hp ↦ fun hnpq ↦ absurd (And.intro hp hq) hnpq ) 
            (fun hnq ↦ fun _ ↦ fun _ ↦ Or.inr hnq) 
    )

    (
    Or.elim (Classical.em q) 
    (fun _ ↦ fun hnp ↦ fun _ ↦ Or.inl hnp)
    (fun _ ↦ fun hnp ↦ fun _ ↦ Or.inl hnp)
    )
example : ¬(p → q) → p ∧ ¬q := 
  fun hnpq ↦ 
    Or.elim (Classical.em p)
            (fun hp ↦ And.intro (hp) (fun hq ↦ hnpq (Function.const p hq)))
            (fun hnp ↦ False.elim (hnpq (falseAntecedent p q hnp)))
example : (p → q) → (¬p ∨ q) := 
  fun hpq ↦ Or.elim (Classical.em p) (fun hp ↦ Or.inr (hpq hp)) (fun hnp ↦ Or.inl hnp)
example : (¬q → ¬p) → (p → q) := 
  fun hnqnp ↦ fun hp ↦ 
  Or.elim (Classical.em q) (fun hq ↦ hq) (fun hnq ↦ absurd (hp) (hnqnp hnq))

example : p ∨ ¬p := Classical.em p

example : (((p → q) → p) → p) := 
  fun hpqp ↦ Or.elim (Classical.em q)
                     (fun hq ↦ hpqp (trueConsequent p q hq))
                     (fun hnq ↦ 
                     Or.elim (Classical.em p)
                             (fun hp ↦ hp)
                             (fun hnp ↦ 
                             hpqp (falseAntecedent p q hnp)))

example : ¬(p ↔ ¬p) :=  
  fun hpnp ↦ 
  have hnp : ¬p := fun hp ↦ absurd hp (hpnp.mp hp)
  have hp : p := hpnp.mpr hnp
  absurd hp hnp


Conclusion 
"adf
"

/- Use these commands to add items to the game's inventory. -/

--NewTactic 
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

