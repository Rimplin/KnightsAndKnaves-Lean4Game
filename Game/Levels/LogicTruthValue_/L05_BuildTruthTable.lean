import Game.Metadata

World "LogicTruthValue_"
Level 5
Title "asdfasdf"
variable {P Q R : Prop}

variable {emTruth : (P : Prop) → P = True ∨ P = False}
#check emTruth

Introduction "You can consider each calc block as its own exercise."
/-

build truth table for expression (after introducing/defining the truth tables for the logical connectives involved, this could be used in two consecutive levels to show equivalence of two propositional statements, this would be useful for propositional expressions that have no rules in mathlib). 

----

to make it work, either split each case into its own level( which sucks because the structure of the proof is lost), or try something with lists /inductive types or conjunction of implications with the skeleton already prepared and comments to indicate what the goal is.(maybe show goals thing would be useful for this...).

-/

  --pick_goal
  --on_goal
  /-
  cases emTruth P
  · cases emTruth Q
    · show (P ∨ ¬Q = True)

    · _
  · cases emTruth Q
    · _

    · _

  show (P ∨ P = True)
 -/ 
--inductive 
#check or_true
#check true_or
#check or_comm

#check not_false
#check not_not
Statement :
  ((P = True ∧ Q = True) → (¬P ∨ Q) = True) 
∧ ((P = True ∧ Q = False) → (¬P ∨ Q) = False)
∧ ((P = False ∧ Q = True) → (¬P ∨ Q) = True)
∧ ((P = False ∧ Q = False) → (¬P ∨ Q) = True)
:= by {
  --repeat (first | constructor <;> constructor)
  Template
    try constructor <;> try constructor <;> try constructor
    
    · intro h
      sorry
      
    · intro h
      sorry

    · intro h
      sorry
    · intro h
      sorry
} 
 /-

  Template
    try constructor <;> try constructor <;> try constructor
    
    · intro h
      calc 
      /-  (¬P ∨ Q) = (¬P ∨ True) := by 
          rw [h.right]
        _ = True := by apply or_true
      -/ 
        (¬P ∨ Q) = (¬True ∨ Q) := by rw [h.left]
        _ = True := by rw [not_true_eq_false,false_or,h.right]
      
    · intro h
      calc
        (¬P ∨ Q) = (False ∨ False) := by rw [h.left,h.right,not_true]
        _ = False := by rw [or_false]

    · intro h
      calc
        (¬P ∨ Q) = (¬P ∨ True) := by rw [h.right]
        _ = True := by rw [or_true]

    · intro h
      calc 
        (¬P ∨ Q) = (True ∨ Q) := by rw [h.left,not_false_eq_true]
        _ = True := by rw [true_or]

 -/
example : ¬P ∨ Q = True ↔ ¬P = True ∨ Q = True := by 
  constructor
  · intro h
    cases h
    · left
      tauto
    · right
      tauto

  · sorry

Conclusion
"
Here's what you proved in truth table form: 
$
\\begin{array}{|c c|c|} 
\\hline
P & Q & ¬P ∨ Q \\\\
\\hline
T & T & T \\\\
T & F & F \\\\
F & T & T \\\\
F & F & T \\\\
\\hline
\\end{array}
$
The expression is `False` when `P` is true and `Q` is false, being false otherwise.
Look familiar? 
$
\\begin{array}{|c c|c|} 
\\hline
P & Q & P → Q \\\\
\\hline
T & T & T \\\\
T & F & F \\\\
F & T & T \\\\
F & F & T \\\\
\\hline
\\end{array}
$
"

NewTactic «try» 
NewTheorem false_or or_false not_true not_false_eq_true not_true_eq_false
