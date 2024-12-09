/-
Introduction 
"
# examples of propositions
'The Lean theorem prover had a 4.70 release' is a true statement. After denoting this statement with `P`, we can say that `P` is true.

'World War 2 ended in 1950' is a false statement. It ended in 1945. After denoting this statement with `Q`, we can say that `Q` is false.

These are called atomic propositions. You will also learn how to make compound propositions from atomic propositions using logical connectives.

# quick overview

## proving statements involving logical connectives
Every logical connective has an introduction rule which introduces a new expression involving propositions with that connective.

## unpacking information from a complicated propositional statement
Logical connective has some 'elimination' or 'unpacking rule' which unpacks the information within that complicated expression.

# Building New Propositions From Previous Ones

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
Combining these two prpositions together gives us the proposition `p ∧ q` which translated to English: 'The official language of France is french `And` the official language of Germany is german'. Because the two propositions connected by the `And` are true, then the entire statement is true as well. 

# truth table 
The truth table of a logical connective illustrates the rule for that logical connective , i.e the truth value of the compound statement depending on the truth value of the atomic propositions.
"
-/
