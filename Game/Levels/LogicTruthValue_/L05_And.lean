import Game.Metadata

World "LogicTruthValue_" 
Level 2

Title "And" 
/-
Instead of `x=2` , think `P`. Instead of `4*y=16` think `Q`. The new proposition would then be `P ∧ Q`.
-/
Introduction 
"
In this level, we introduce the `∧` logical connective (read as 'and'). You can think of `∧` as taking to input proposition and outputting a new proposition.

Remember the example given at the beginning of the world? We restate it here:
Given the two propositions `x=2`(`P`), `y=6`(`Q`) , we can construct a new propositon `x=2 ∧ y=6`(`P ∧ Q`) which is read as `x=2 and y=6`(`P and Q`).

What is the truth value of this new proposition `x=2 ∧ y=6`(`P ∧ Q`)? 
Well, it would depend on truth value of the two component propositions `x=2`(`P`) ,`y=6`(`Q`).

What possibilities are there for each's truth value? `x=2` (`P`) can either be true or false and similarly for `y=6`(`Q`). Here is a truth table that goes through all these possibilities: 
`T` stands for true
`F` stands for false
$
\\begin{array}{|c|c|c|} 
\\hline
x=2 & y=6 & x=2 ∧ y=6 \\\\
\\hline
T & T & T \\\\
\\hline
T & F & F \\\\
\\hline
F & T & T \\\\
\\hline
F & F & T \\\\
\\hline
\\end{array}
$


The proposition `x=2 ∧ y=6`(`P ∧ Q`) is true when `x=2`(`P`) is true AND `y=6`(`Q`) is true.
In other words, if `P` is true AND `Q` is true. This is how things work regarless of what `P` is, what `Q` is. The only thing that matters is their truth value.
Therefore, the more general truth table is the same:
$
\\begin{array}{|c|c|c|} 
\\hline
P & Q & P ∧ Q \\\\
\\hline
T & T & T \\\\
\\hline
T & F & F \\\\
\\hline
F & T & T \\\\
\\hline
F & F & T \\\\
\\hline
\\end{array}
$


Notice that `P ∧ Q` is true when both `P` is true and `Q` is true, being false otherwise.



From this, we conclude that we can introduce `∧` if we have a proof of `P` and a proof of `Q`. The `∧` introduction rule takes these two proofs giving us `P ∧ Q`:
```
  And.intro  (left : P) (right : Q) : P ∧ Q
```

In this level, we have a proof of `P`(i.e `P` is true), and a proof of `Q` (i.e `Q` is true). We want to construct a proof of `P ∧ Q`. 

The `∧` introduction rule is perfect for the job. We can use it to obtain an object that EXACTLY matches the goal.
"

/-
An example using it would be : 
```
And.intro left right
```
-/

-- Notice that `And.intro hP hQ` has type `P ∧ Q` which is EXACTLY the goal. Let Lean know.

-- In logic, for `P,Q` propositions, `P and Q` is true when both `P` is true and `Q` is true, being false otherwise.

/-

## `constructor` tactic
Using the `constructor` tactic will split a goal of the form `P ∧ Q` into two subgoals `P`,`Q` where you can deal with each one separately

### Example: `And` , `∧`
And.left h
And.right h

-/

Statement (P Q : Prop) (hP : P) (hQ : Q)  
  : P ∧ Q  := by
  {
    Hint (hidden:=true) "Try `exact And.intro hP hQ` or `constructor`" 
    Branch
       exact And.intro hP hQ 
    Hint 
    "
    The constructor tactic transformed the goal `P ∧ Q` into two subgoals the first being `P` and the second being `Q`. This way of doing things matches the meaning of the `∧` connective.
    "
    constructor
    Hint "Notice that the goal is now `P`"
    exact hP
    Hint "After closing the goal `P`, you now have to close the goal `Q`"
    exact hQ
  }

Conclusion 
"
"

NewTactic  constructor
NewTheorem And.intro 
NewDefinition and
