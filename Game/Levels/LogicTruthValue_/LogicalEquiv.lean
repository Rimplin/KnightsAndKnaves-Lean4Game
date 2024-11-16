import Game.Metadata


World "LogicTruthValue_" 
Level 7

Title "" 

#check propext
  -- axioms and computations, theorem proving in lean 4
Introduction 
"
`P ↔ Q`  is defined as `(P → Q) ∧ (Q → P)`. But what does it mean? Let's construct its truth table and find out.(make it as the level itself??)

Remember,
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

$
\\begin{array}{|c c|c|} 
\\hline
Q & P & Q → P \\\\
\\hline
T & T & T \\\\
T & F & F \\\\
F & T & T \\\\
F & F & T \\\\
\\hline
\\end{array}
$

put ∧ truth table

The result is
$
\\begin{array}{|c c|c|} 
\\hline
P & Q & P → Q & Q → P & P → Q ∧ Q → P\\\\
\\hline
T & T & T & T & T \\\\
T & F & F & T & F \\\\
F & T & T & F & F \\\\
F & F & T & T & T \\\\
\\hline
\\end{array}

So, `P ↔ Q` is true when `P,Q` are true or `P,Q` are false, i.e when `P` and `Q` have the same truth value. Therefore, `P` and `Q` are equivalent from a truth value perspective regardless what the statement of `P` and of `Q` is.

-- so now i need to mention modus ponens explicitly, put it as an inference rule
To extract for example the forward direction `P → Q` from `h :P ↔ Q`, you do `h.mp`. This is a modus ponens version for `↔`. The reversed version `h.mpr` gives `Q → P`
$
"

#check Iff.mpr
inductive Solution (Knight : Finset Inhabitant) (Knave : Finset Inhabitant)
| submit (h : A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) : Solution (Knight) (Knave)
inductive Submit (P Q : Prop) 
| submit1 (h' : P)  (h'' : Q) (h : P ↔ Q) :Submit P Q
| submit2 (h' : P)  (h'' : ¬Q) (h : ¬(P ↔ Q)) :Submit P Q
| submit3 (h' : ¬P)  (h'' : Q)(h : ¬(P ↔ Q) ) :Submit P Q
| submit4 (h' : ¬P)  (h'' : ¬Q)(h : P ↔ Q) :Submit P Q
/-
1. type mismatch when assigning motive
     fun t => x✝ = t → Submit P Q
   has type
     P ∨ ¬P → Type : Type 1
   but is expected to have type
     P ∨ ¬P → Prop : Type
Statement (P Q : Prop)
  : Submit P Q := by

  {
    #check em
    cases em P
  }
-/

-- represent the truth table as a conjunction of implications, would need to resort to the truh value perspective and deal with those rules manually, maybe put it in an optional world.

Statement (P Q : Prop) :
(P ∧ Q → (P ↔ Q)) ∧ (P ∧ ¬Q → (¬ (P ↔ Q) ) ) 
∧ (¬P ∧ Q → (P ↔ Q)) ∧ (¬P ∧ ¬Q → (¬ (P ↔ Q) ) ) 
:= by 
  constructor
  · sorry
  · constructor
    · sorry
    · constructor
      sorry
      sorry

Conclusion 
"
"
