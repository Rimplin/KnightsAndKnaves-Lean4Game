import Game.Metadata


World "Logic" 
Level 5

Title "asdf" 

Introduction 
"
# Natural Language Examples
Let `P` denote the assertion 'Today is Monday'. `¬P` would then denote the assertion 'Today is not Monday'. You could also say that `¬P` denotes 'Today is Tuesday or Wednsday or Thursday or Friday or Saturday or Sunday'. Both assertions express the same thing (assuming there are 7 days of the week and these are their names) so either one is acceptable.

# Truth Table
We want an operator which flips the value of `P`. In other words, if `P` were true then `¬P` would be false and vice versa. 
Lets call this operator `not` represented as `¬`. This is what the truth table would look like.
$
\\begin{array}{|c|c|} 
\\hline
P & ¬P \\\\
\\hline
T & F  \\\\
F & T  \\\\
\\hline
\\end{array}
$
But we don't need to introduce a new symbol, it can be defined in terms of what we already know.
Defining `¬P` as `P → False` would accomplish this. Notice that this definition is an implication which you have learned to deal with in the previous level and that the two truth tables are identical which means this is a correct definition.
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

But what is `False` exactly?
For now, just know that `False` is a type that has no introduction rule and that proving `False` means deriving a contradiction. So, to prove `¬p` , you must assume `p` and derive a contradiction. We will explain in more detail what is meant by 'contradiction'.

To emphasize the fact that negation is an implication, you have to go through this simple level.
"

variable {q : Prop}
Statement (hp:p) (hnp:¬p)
  :  False := by

  {
    exact hnp hp
  }

Conclusion 
"
In the next level, we will explore what it means to have proven `False`(pretty bad, or pretty good depending on how you look at it).
"

/- Use these commands to add items to the game's inventory. -/

--NewTactic 
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

