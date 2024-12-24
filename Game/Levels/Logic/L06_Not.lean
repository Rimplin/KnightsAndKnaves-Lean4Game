import Game.Metadata

World "Logic"
Level 6

Title "Not Connective, ¬"

/-
# What is `False` exactly? 

Proving a proposition and its negation is a special case of 'deriving a contradiction' because we have proven `p ∧ ¬p` which is always false. A logical system that has this quality is called an inconsistent system.

## But what is `False` exactly?(now we know what `False` is from the truth value perspective so this would need a rewrite in logic world, no it doesn't because we were dealing with `= False` but now we are dealing with `→ False`).
For now, just know that `False` is a type that has no introduction rule and that proving `False` means deriving a contradiction. So, to prove `¬p` , you must assume `p` and derive a contradiction. We will explain in more detail what is meant by 'contradiction'.
-/

Introduction
"
In this level we introduce the negation, the `¬` connective (read as 'not').

Notice that this is the first logical connective that applies on one proposition only and not two.

The job of this connective(as the name implies), is to negate a proposition meaning that:
- For `P` true, `¬P` is false.
- For `P` false, `¬P` is true.

In truth table form:
$
\\begin{array}{|c|c|} 
\\hline
P & ¬P \\\\
\\hline
T & F \\\\
F & T \\\\
\\hline
\\end{array}
$

Notice that since `P` is true, `¬P` should be false but in this proof state it is true (by `hnP`). This is a contradiction. The goal is to prove `False` which means to prove a contradiction.

Note that we don't need to introduce a new symbol to define negation, it can be defined in terms of what we already know.

Consider the following truth table: 
$
\\begin{array}{|c|c|} 
\\hline
P & P → False \\\\
\\hline
T & F  \\\\
F & T  \\\\
\\hline
\\end{array}
$

Notice that regardless of the truth value of `P`, the two propositions `¬P` and `P → False` have the same truth table. Therefore, they can be used interchangeably.(we say that these two expressions are logically equivalent, but let's leave this to a future level)

What `¬P` means is that if `P` were true, then we can deduce a contradiction. We know that `P` is true. Therefore, we can prove a contradiction which is the goal.

To see `¬P` in its implication form, you can do `unfold Not at hnP` to unfold the definition of `¬`.

"

/-
The empty type. It has no constructors.
`False` is the empty proposition, thus it has no introduction rule. It represents a contradiction.
What is a contradiction? Well, it is a propostional statement that is false for all possible values of its variables. Constructing a term(i.e a proof) of this type is proving something that is false. The standard example of a contradiction is the following: 

Another meaning for the term contradiction to refer to the assertion or proof of a propositional statement that is false for all possible values of its variables. We will use both interchangeably. So, deriving a contradiction means constructing such a proof.

# What is `False` exactly? 

## How to prove `False` and what are the consequences?
Proving a proposition and its negation is a special case of 'deriving a contradiction' because we have proven `p ∧ ¬p` which is always false. A logical system that has this quality is called an inconsistent system.

## Principle of explosion
Moreover, `False` has no introduction rule , so the reasoning described above is the only way to obtain an object of type `False`. If you were able to find `h:False` i.e prove `False` then our system is worthless because we can prove anything. To reiterate, such a system would be called an inconsistent system because of a contradiction.
-/

#check not_of_eq_false
Statement {P: Prop}
{hP : P} {hnP : ¬P}
: False := by{
    Hint (hidden:=true)
   "Remember that an implication acts like a function, that takes a proof of whats on the left hand returning a proof of whats on the right hand side.

For this level, `¬P` being true tells us that a proof of `P` gives us a proof of `False`. We have a proof of `P`. Therefore we can obtain a proof of `False` which is the goal."
    unfold Not at hnP

    Hint (hidden:=true)
   "Remember that an implication acts like a function, that takes a proof of whats on the left hand returning a proof of whats on the right hand side.

For this level, `¬P` being true tells us that a proof of `P` gives us a proof of `False`. We have a proof of `P`. Therefore we can obtain a proof of `False` which is the goal."
    exact hnP hP 
 } 

Conclusion 
"
In the next level, we will explore what it means to have proven `False`.
"

/-

circular explanation below, P ∧ ¬P is false but proving it true. P is true but having ¬P proves it false.
To emphasize the idea of what 'contradiction' means, consider the following truth table:
$
\\begin{array}{|c|c|} 
\\hline
P & ¬P & P ∧ ¬P\\\\
\\hline
T & F & F \\\\
F & T & F \\\\
\\hline
\\end{array}
$

In the current proof state, we know that `P ∧ ¬P` is true but notice from the truth that `P ∧ ¬P` is always false regardless of the value of `P`. A contradiction is when a proposition is true and false at the same time, in other words, when for a `P : Prop` we have
```
hP : P   proof that P is true
hnP : ¬P proof of ¬P is true i.e P is false
```
-/
NewTactic unfold
