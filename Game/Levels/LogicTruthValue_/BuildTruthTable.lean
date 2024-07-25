import Game.Metadata

variable {P Q R : Prop}

variable {emTruth : (P : Prop) → P = True ∨ P = False}
#check emTruth

Introduction "You can consider each calc block as its own exercise."
/-
to make it work, either split each case into its own level( which sucks because the structure of the proof is lost), or try something with lists /inductive types or conjunction of implications with the skeleton already prepared and comments to indicate what the goal is.(maybe show goals thing would be useful for this...).
-/

--inductive 
example :
  (P = True ∧ Q = True → ¬P ∨ Q = True) 
∧ (P = True ∧ Q = False → ¬P ∨ Q = False)
∧ (P = False ∧ Q = True → ¬P ∨ Q = True)
∧ (P = False ∧ Q = False → ¬P ∨ Q = True)
:= by 
  --repeat (first | constructor <;> constructor)
  try constructor <;> try constructor <;> try constructor
  
  · intro h
    
  · intro h

  · intro h
  · intro h
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
