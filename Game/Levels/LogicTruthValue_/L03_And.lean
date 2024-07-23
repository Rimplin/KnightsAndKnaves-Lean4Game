import Game.Metadata

variable (P Q R : Prop)

World "LogicTruthValue_" 
Level 3

Title "And" 

Introduction 
"
In this level, we will learn about the `∧` logical connective, known as 'And'.
In logic, for `P,Q` propositions, `P ∧ Q` is true when both `P` is true and `Q` is true, being false otherwise.

# Logical Connectives
It is important to note that connecting two proposition via a logic connective results in a proposition as well. This proposition, like any other proposition, has a truth value. This truth value depends on the truth value of the propositions it was built out of and the rules of the logical connective. This is clearly illustrated in a truth table. 

# Truth table
The truth table of a logical connective illustrates the rule for that logical connective , i.e the truth value of the compound statement depending on the truth value of the propositions it connects.
The following truth table illustrates this for the previously discussed `∧` connective.
`T` stands for true
`F` stands for false
$
\\begin{array}{|c c|c|} 
\\hline
P & Q & P ∧ Q \\\\
\\hline
T & T & T \\\\
T & F & F \\\\
F & T & F \\\\
F & F & F \\\\
\\hline
\\end{array}
$
Notice that `P ∧ Q` is true when both `P` is true and `Q` is true, being false otherwise.

## example

Let `p` denote the proposition 'The official language of France is french'(which is true).
Let `q` denote the prposition 'The official language of Germany is german'(which is true as well).
Combining these two prpositions together gives us the proposition `p ∧ q` which translated to English: 'The official language of France is french `And` the official language of Germany is german'. Because the two propositions connected by the `And` are true, then the entire statement is true as well. It's not hard to see that one of or both `p` or `q` being false would make `p ∧ q` false. In other words, `p ∧ q` is true when `p` is true and `q` is true. It is false otherwise.


# `And` Introduction rule
In Lean, to prove `P ∧ Q`, you need a proof of `P` and a proof of `Q`.
The `And` introduction rule will enable us to prove statements involving `∧`.
For example, given the following proof state:
```
hP : P
hQ : Q
⊢ P ∧ Q
```
We can close the goal by:
```
exact And.intro hP hQ
```


## first way
Giving these two proofs to the And introduction rule will construct a proof of `P ∧ Q`.

Here's the type of `And.intro`:
```
  And.intro  (left : P) (right : Q) : P ∧ Q
```
where `P Q : Prop`

## second way
Using the `constructor` tactic will split a goal of the form `P ∧ Q` into two subgoals `P`,`Q` where you can deal with each one separately

### Example: `And` , `∧`
And.intro
And.left h
And.right h


The atomic propositions in the compound proposition `p ∧ q` are : `p`, `q`. Of course, `p ∧ q` can be used to construct more complicated propositions.

"

--variable {p : BooleanAlgebra Prop}
--#check p.himp_eq P Q

/-- testing wow -/
Statement (hP : P=True) (hQ : Q=True) (hPQ: P ∧ Q)
  : (P ∧ Q) = True  := by

  {
    -- no theorem to directly get this, maybe do a calc proof??? compare that to other approaches of logical proof.
    #check True.intro
    #check True

    #check hP
    #check P=True
   -- rw [hP,hQ]
   -- apply and_true 
    Template
      calc 
        (P ∧ Q) = (True ∧ Q) := by rw [hP]
        _ = (True ∧ True) := by rw [hQ] 
        _ = True := by exact and_true True

--    tauto 
 --   refine 

--    apply?

    --Hint (hidden:=true) "Try `exact And.intro hP hQ` or `constructor`" 
    --Branch
    --   exact And.intro hP hQ 
    --constructor
    --Hint "Notice that the goal is now `P`"
    --exact hP
    --Hint "After closing the goal `P`, you now have to close the goal `Q`"
    --exact hQ
  }





Conclusion 
"
The constructor tactic transformed the goal `P ∧ Q` into two subgoals the first being `P` and the second being `Q`. This way of doing things matches the meaning of the `∧` connective.
"

/- Use these commands to add items to the game's inventory. -/

NewTactic  constructor
NewTheorem And.intro 
-- NewDefinition Nat Add Eq
