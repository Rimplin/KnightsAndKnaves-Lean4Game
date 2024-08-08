import Game.Metadata


World "Logic" 
Level 8

Title "Principle Of Explosion" 

Introduction 
"
Prove princpiple of explostion from truth value perspective...

From `False` anything follows.
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

| P | Q | P & Q |
|—|—|—|
| T | T | T |
| T | F | F |
| F | T | F |
| F | F | F |


$
\\begin{array}{|c c|c|} 
\\hline
a & b & F \\\\
\\hline
0 & 0 & 0 \\\\
0 & 1 & 0 \\\\
1 & 0 & 0 \\\\
1 & 1 & 1 \\\\
\\hline
\\end{array}
$


$\\displaystyle {\\frac {P\\lor Q,\\neg P}{\\therefore Q}}$

"

-- explanation
/-
we have proved a statement that is not true. Since we proved it, now it's also true? Let's denote this proposition as `Q`. So we have `Q ∧ ¬Q`. What does the truth table for this expression look like for any proposition `R`?
$
\\begin{array}{|c|c|} 
\\hline
R & ¬R & R ∧ ¬R \\\\
\\hline
T & F & F \\\\
F & T & F \\\\
\\hline
\\end{array}
$
This statement is always false regardless of the truth values of `R` but we were able to prove such a statement. How can this be?
This is very bad because of the following: 
For any propositioin `P`,
$
\\begin{array}{|c|c|} 
\\hline
P & False → P \\\\
\\hline
T  & T \\\\
F  & T \\\\
Notice that the implication `False → P` is always true. This means that proving `False` amounts to proving everything!!!
The system you are working with quickly becomes trivial and loses its value. If you're objective is to reach truth, then there is nothing to do here because everything is true. There is nothing to study or investigate, its all true!
\\hline
\\end{array}
$

This is the meaning of `False ≠ True`, proving `False = True` gives a contradiction. A contradiction is when `p` and `¬p` are both true. `False ≠ True` is always true regardless of proof state, but in this state we also have `False = True` giving us a contradiction. Notice that even our starting point was of contradiction, where we had `p = True` and `p = False` i.e `¬p = True`.
-- truth table of `p ∧ ¬p`
-/



-- need to have disjunctive syllogism as an already established primitive , disjunctive syllogism would have to be explained here as well which might be a bit too much??
/-
--will not prove, can be easily explained in a reasonable and convincing way
-/


  /-
   cases h 
   have := np h_1  
   contradiction
   -/
#check imp_false
#check eq_false
#check eq_false'
#check implies_true
#check true_implies
#check true_imp_iff
#check false_implies
#check true_iff
#check false_iff
#check iff_false
#check Or.elim
variable {P Q:Prop} 

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

example : ¬ (¬ P) ↔ P := by
  constructor
  · intro h
    push_neg at h
    assumption

  · intro h
    push_neg
    assumption


Conclusion 
"
We have proven that `P ∧ ¬P → Q` for any proposition `Q`. since `P ∧ ¬P` is always false, then the implication proved becomes `False → Q`.

From contradiction, anything follows.
There are more examples of contradictions like 
¬(P ∨ ¬P)

$
\\begin{array}{|c c|c|} 
\\hline
P & ¬P & P ∨ ¬P & ¬(P ∨ ¬P) \\\\
\\hline
T & F & T & F \\\\
F & T & T & F \\\\
\\hline
\\end{array}
$

You could have also solved it by just writing `contradiction`. Contradiction is a tactic that detects if you have contradictory assumptions and if so, closes the goal. Try it if you want.
"

/- Use these commands to add items to the game's inventory. -/

NewTactic contradiction
-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

