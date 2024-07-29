import Game.Metadata


World "LogicTruthValue_" 
Level 

Title "" 

Introduction 
"
"

variable {emTruth : (P : Prop) → P = True ∨ P = False}
  example : (p ∧ ¬p) = False := by {
   cases emTruth p
   · rw [h]
     rw [not_true_eq_false]
     rw [and_false]

   · rw [h]
     rw [false_and]
}

#check true_ne_false
#check not_true_eq_false
#check refl
--#check true_eq_true
#check eq_self
#check eq_true
-- p ∧ ¬p is a contradiction
  example : ((p = True) ∧ (p = False)) = False := by {
   cases emTruth p
   · rw [h]
     rw [eq_self]
     rw [true_and]
     have := true_ne_false
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
Statement 
  :  := by

  {

  }





Conclusion 
"
Note that we have not obtained a term of type `False` in our proof. We have only proved the above equality. To obtain `False` in our proof state, we would need to have a term of type `p ∧ ¬p` and then use the above theorem rewriting the previous expression to `False`. What happens if we have `False` in our proof state.(now explain stuff about `False` no introduction rule and so on).
"

/- Use these commands to add items to the game's inventory. -/

--NewTactic 
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
