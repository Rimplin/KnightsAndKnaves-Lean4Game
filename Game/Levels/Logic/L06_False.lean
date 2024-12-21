import Game.Metadata

variable {emTruth : (P : Prop) → P = True ∨ P = False}
-- ∀ {p : Prop}, p = True → p = False → False
example (hp:p=True) (hnp:p=False) (hnnp:¬p=True) (h' : (p = True) → (False = True) ) : False := by 

{
  unfold Not at hnnp
  have : (p=True) ∧ (p=False) := by exact And.intro hp hnp
  have this2: False :=by exact hnnp hp
  -- true regardless of proof state i.e true in every proof state, introduce it in a previous level and then when i come here, i can form the term on the left and rewrite to get `False`.
  have this2: p ≠ True := by rw [hnp]; apply false_ne_true
  exact this2 hp
}

example (hp:p) (hnp:¬p)
  :  False := by
  {
    -- This is the same as saying that we have a proof of `p` and we want to prove `False`
    -- So, we can use `hp` to prove `False`
    Hint (hidden:=true) "If you feel like seeing the implication definition of ¬ in the proof state would provide more clarity and make it easier to solve upcoming problems, you can always unfold ¬ to its implication form. Try `unfold Not at hnp`."
    unfold Not at hnp 
    Hint "Now, this is just like the previous level"
    exact hnp hp
  }
