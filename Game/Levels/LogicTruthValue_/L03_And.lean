import Game.Metadata

variable (P Q R : Prop)

World "LogicTruthValue_" 
Level 3

Title "And" 

Introduction 
"
In this level, we will learn about the `∧` logical connective, known as 'And'.
In logic, for `P,Q` propositions, `P and Q` is true when both `P` is true and `Q` is true, being false otherwise.


## Logical Connectives
It is important to note that connecting two proposition via a logic connective results in a proposition as well. This proposition, like any other proposition, has a truth value. This truth value depends on the truth value of the atomic propositions and the rules of the logical connective. This point will be reiterated and hopefully fully materialize in your head as you deal with various logical connectives and as we discuss truth tables(see below for an example).

Every logical connective has an introduction rule which introduces a new expression involving propositions with that connective and some 'elimination' or 'unpacking rule' which unpacks the information within such an expression.

### Example: `And` , `∧`
And.intro
And.left h
And.right h

As an example, we present the `∧` logical connective.
Let `p` denote the proposition 'The official language of France is french'(which is true).
Let `q` denote the prposition 'The official language of Germany is german'(which is true as well).
Combining these two prpositions together gives us the proposition `p ∧ q` which translated to English: 'The official language of France is french `And` the official language of Germany is german'. Because the two propositions connected by the `And` are true, then the entire statement is true as well. It's not hard to see that one of or both `p` or `q` being false would make `p ∧ q` false. In other words, `p ∧ q` is true when `p` is true and `q` is true. It is false otherwise.

The atomic propositions in the compound proposition `p ∧ q` are : `p`, `q`. Of course, `p ∧ q` can be used to construct more complicated propositions.

# Two ways of dealing with ∧ in the goal(Try both!)
In Lean, to prove `P ∧ Q`, you need a proof of `P` and a proof of `Q`.
## first way
Giving these two proofs to the And introduction rule will construct a proof of `P ∧ Q`.

Here's the type of `And.intro`:
```
  And.intro  (left : P) (right : Q) : P ∧ Q
```
where `P Q : Prop`

## second way
Using the `constructor` tactic will split a goal of the form `P ∧ Q` into two subgoals `P`,`Q` where you can deal with each one separately


# truth table 
The truth table of a logical connective illustrates the rule for that logical connective , i.e the truth value of the compound statement depending on the truth value of the atomic propositions.

The following truth table illustrates this for the prevously discussed `∧` connective.
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

"

--variable {p : BooleanAlgebra Prop}
--#check p.himp_eq P Q
Statement (hP : P=True) (hQ : Q=True) (hPQ: P ∧ Q)
  : (P ∧ Q) = True  := by

  {
    -- no theorem to directly get this, maybe do a calc proof??? compare that to other approaches of logical proof.
    #check True.intro
    #check True
   -- rw [hP,hQ]
   -- apply and_true 

  --  calc 
  --    (P ∧ Q) = (True ∧ Q) := by rw [hP]
  --    _ = (True ∧ True) := by rw [hQ] 
  --    _ = True := by exact and_true True

    #check hP
    #check P=True
--    tauto 
    refine 

    apply?
    Hint (hidden:=true) "Try `exact And.intro hP hQ` or `constructor`" 
    Branch
       exact And.intro hP hQ 
    constructor
    Hint "Notice that the goal is now `P`"
    exact hP
    Hint "After closing the goal `P`, you now have to close the goal `Q`"
    exact hQ
  }





Conclusion 
"
The constructor tactic transformed the goal `P ∧ Q` into two subgoals the first being `P` and the second being `Q`. This way of doing things matches the meaning of the `∧` connective.
"

/- Use these commands to add items to the game's inventory. -/

NewTactic  constructor
NewTheorem And.intro 
-- NewDefinition Nat Add Eq

