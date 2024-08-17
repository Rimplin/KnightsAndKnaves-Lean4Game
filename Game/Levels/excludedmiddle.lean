import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

/- there is a theorem in Mathlib for this, but we use `have` to create smaller goals to bypass it -/

example [DecidableEq α] (S : Finset α) (e : α) : (insert e S).card ≤ S.card + 1 := by

  if h : e ∈ S then

    have : insert e S = S := Finset.insert_eq_self.mpr h

    rw [this]

    exact Nat.le_add_right (Finset.card S) 1

  else

    have : S.card + 1 = (insert e S).card := (Finset.card_insert_of_not_mem h).symm

    rw [this]

-- more info https://lobste.rs/s/hwjv0f/beginner_s_companion_theorem_proving#c_jc4wbc
