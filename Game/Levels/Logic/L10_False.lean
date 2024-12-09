import Game.Metadata

Introduction 
"
In this level, we will prove a statement that is always false i.e `= False`. To do this, we take all possible values of the propositional variable involved and show that the expression always evaluates to `False`.

This is a proof by cases. By taking all possible cases and showing a certain statement in each case, we have proven this statement is true. Even more, we have shown its true regardless of the assumptions in the proof state.

--- 
two ways of showing that `P` and `¬P` is a contradiction, this is the first but a second way if introducing law of excluded middle and saying which is done ehre as well.
"

variable {emTruth : (P : Prop) → P = True ∨ P = False}
example : (p ∧ ¬p) = False := by {
  -- to do, make a cases `Template` , with comments as hints instead of Hint
    cases emTruth p 
    · sorry
-- hint 1

-- asdf
-- asdf2
-- asdf3
    · sorry
}
/-
weird hint behavior...
hint doesn't show up unless you type first, which defeats the whole point

  Template
    cases emTruth p
    · Hole
        Hint "some hint"
        rw [h]
        Hint "hitn 2"
        rw [not_true_eq_false]
        sorry
    -- hint 1

-- hint 2

    · Hole
        sorry
-- hint 3
-- hint 4

--hint 5


 Template 

   cases emTruth p
   · Hole
     --Hint "First replace"
     rw [h]
     --Hint (hidden := true) "not_true_eq_false"
     rw [not_true_eq_false]
     rw [and_false]

   · Hole
     Hint "Second Replace"
     rw [h]
     rw [false_and]
-/

/-

   cases emTruth p
   · rw [h]
     rw [not_true_eq_false]
     rw [and_false]

   · rw [h]
     rw [false_and]
-/

#check true_ne_false
#check not_true_eq_false
#check refl
#check eq_self
-- p ∧ ¬p is a contradiction
  example : ((p = True) ∧ (p = False)) = False := by {
   cases emTruth p
   · rw [h]
     rw [eq_self]
     rw [true_and]
     have := true_ne_false
     -- use simp only to unfold everything
     unfold Not at this

     -- difference between equality and equivalence (?)
     have this2 : False → (True = False) := by {
      intro h
      contradiction
     }
     have this3 := Iff.intro this this2
     rw [this3]
   /-
     rw [h]
     have : (True=True)=True := by apply eq_self
     rw [this]
     rw [true_and] 
     by_contra h''
     have this2:= true_ne_false
     rw [←not_true_eq_false] at h''
    -/  
   · rw [h]
     rw [eq_self]
     rw [and_true]
     have := true_ne_false
     unfold Not at this
     #check Trans.trans
     have this21:(False = True) → False := by
      intro h'
      symm at h'
      exact this h'

     -- difference between equality and equivalence (?)
     have this22 : False → (False = True) := by {
      intro h
      contradiction
     }
     have thisexp :Implies (True = False)  (False = True) := Implies.trans this this22
     -- find cleaner way to do transitivity of implication, there is Implies.trans but not available in latest version, seems like the entire Implies namespace was nuked. Eq.trans is avaialble in both versions however so maybe introduce that in prev levlel and then do a thereom of implication trans. moreover, could be introduced in calc world which is (?) required now and not optional.
     #check Implies.trans
     unfold Implies at thisexp
     have this3 := Iff.intro this21 this22
     #check trans
     rw [this3]
     --#check Implies
}

Conclusion 
"
To obtain `False` in our proof state, we would need to have a term of type `p ∧ ¬p` and then use the above theorem rewriting the previous expression to `False`.
"
