import Game.Metadata


World "Logic" 
Level 8

Title "Principle Of Explosion" 

Introduction 
"
Otherwise known as 'from contradiction, anything follows'. 
This principle asserts that if you have contradictory assumptions then you can prove anything.
Example of contradictory assumptions:
```
h: P
nh: ¬P
```

Why is this principle valid? Well, this is what you will have to prove in this level. For your convenience, the contradiction tactic will be unlocked after this level so you don't have to do the same steps when there are contradictory assumptions.


you can prove anything. 
False.elim eliminates false and produces an object of any type you want!!!
False implies anything.
"
-- need to have disjunctive syllogism as an already established primitive , disjunctive syllogism would have to be explained here as well which might be a bit too much??
/-
"
$\\displaystyle {\\frac {P\\lor Q,\\neg P}{\\therefore Q}}$
"
--will not prove, can be easily explained in a reasonable and convincing way
-/


variable {P Q : Prop}

theorem disjunctiveSyllogism (h : P ∨ Q) (np : ¬P)
  : Q := by

  {
    apply Or.elim (Classical.em Q)
    intro hQ
    assumption 

    intro hnQ 
    have := And.intro np hnQ
    rw [not_or.symm] at this
    contradiction
  }
  /-
   cases h 
   have := np h_1  
   contradiction
   -/
   
Statement (h : P) (nh : ¬P)
  : Q := by

  {
    have helper : P ∨ Q := Or.inl h
    exact disjunctiveSyllogism helper nh
  }


example : ¬ (¬ P) ↔ P := by
  constructor
  · intro h 
    apply Or.elim (Classical.em P)
    sorry
    sorry

  · sorry

example (P : Prop) : ¬ (¬ P) ↔ P := by
  constructor
  · intro h
    push_neg at h
    assumption

  · intro h
    push_neg
    assumption


Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

NewTactic contradiction
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

