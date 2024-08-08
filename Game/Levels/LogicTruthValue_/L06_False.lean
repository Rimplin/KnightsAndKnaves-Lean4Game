import Game.Metadata


World "Logic" 
Level 5

Title "asdf" 

Introduction 
"
# Truth Table
We want an operator which flips the value of `P`. In other words, if `P` were true then `¬P` would be false and vice versa. 
Lets call this operator `not` represented as `¬`. 

This is what the truth table would look like.
$$
\\begin{array}{|c|c|} 
\\hline
P & ¬P \\\\
\\hline
T & F  \\\\
F & T  \\\\
\\hline
\\end{array}
$$

To emphasize the fact that negation is an implication, you have to go through this simple level.
"

#check false_ne_true
#check False
variable {p : Prop}
variable {emTruth : (P : Prop) → P = True ∨ P = False}
-- type
variable { h: p ∧ ¬p}
theorem hh : False := by 
  exact h.right h.left
#check of_eq_true (eq_true hh)
#check eq_true
#check of_eq_true
-- ∀ {p : Prop}, p = True → p = False → False
example (hp:p=True) (hnp:p=False) (hnnp:¬p=True) (h' : (p = True) → (False = True) ) : False := by 

{
  #check hnnp
  unfold Not at hnnp
  have : (p=True) ∧ (p=False) := by exact And.intro hp hnp
  have this2: False :=by exact hnnp hp
  -- true regardless of proof state i.e true in every proof state, introduce it in a previous level and then when i come here, i can form the term on the left and rewrite to get `False`.
  #check this
  have this2: p ≠ True := by rw [hnp]; apply false_ne_true
  exact this2 hp
  
}

variable {p : Prop}
Statement (hp:p) (hnp:¬p)
  :  False := by

  {
    -- We can use the definition of `¬` to rewrite `hnp` as `p → False`
    -- This is the same as saying that we have a proof of `p` and we want to prove `False`
    -- So, we can use `hp` to prove `False`
    Hint (hidden:=true) "If you feel like seeing the implication definition of ¬ in the proof state would provide more clarity and make it easier to solve upcoming problems, you can always unfold ¬ to its implication form. Try `unfold Not at hnp`."
    unfold Not at hnp 
    Hint "Now, this is just like the previous level"
    exact hnp hp
  }

Conclusion 
"
In the next level, we will explore what it means to have proven `False`(pretty bad, or pretty good depending on how you look at it).
"

/- Use these commands to add items to the game's inventory. -/

NewTactic unfold
-- NewTheorem Nat.add_comm Nat.add_assoc

--DefinitionDoc Not as "¬" 
NewDefinition Not  
--TheoremDoc mul_left_cancel as "mul_left_cancel" in "*"
