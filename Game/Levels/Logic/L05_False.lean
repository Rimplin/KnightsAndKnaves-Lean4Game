import Game.Metadata


World "Logic" 
Level 5

Title "asdf" 

Introduction 
"
# Truth Table
We want an operator which flips the value of `P`. In other words, if `P` were true then `¬P` would be false and vice versa. 
Lets call this operator `not` represented as `¬`. 

This is what the truth table would look like.
$$
\\begin{array}{|c|c|} 
\\hline
P & ¬P \\\\
\\hline
T & F  \\\\
F & T  \\\\
\\hline
\\end{array}
$$

# Natural Language Example

Let `P` denote the assertion 'Today is Monday'. `¬P` would then denote the assertion 'Today is not Monday'. You could also say that `¬P` denotes 'Today is Tuesday or Wednsday or Thursday or Friday or Saturday or Sunday'. Both assertions express the same thing (assuming there are 7 days of the week and these are their names) so either one is acceptable.

# Defining `¬`
But we don't need to introduce a new symbol, it can be defined in terms of what we already know.
Defining `¬P` as `P → False` would accomplish this. 
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
Notice that this definition is an implication which you have learned to deal with in the previous level and that the truth table with `¬P` and the truth table with `P → False` are identical which means this definition captures what we want `¬` to mean.

## But what is `False` exactly?
For now, just know that `False` is a type that has no introduction rule and that proving `False` means deriving a contradiction. So, to prove `¬p` , you must assume `p` and derive a contradiction. We will explain in more detail what is meant by 'contradiction'.

To emphasize the fact that negation is an implication, you have to go through this simple level.
"

variable {p : Prop}
Statement (hp:p) (hnp:¬p)
  :  False := by

  {
    -- We can use the definition of `¬` to rewrite `hnp` as `p → False`
    -- This is the same as saying that we have a proof of `p` and we want to prove `False`
    -- So, we can use `hp` to prove `False`
    Hint (hidden:=true) "If you feel like seeing the implication definition of ¬ in the proof state would provide more clarity and make it easier to solve upcoming problems, you can always unfold ¬ to its implication form. Try `unfold Not at hnp`."
    unfold Not at hnp 
    Hint "Now, this is just like the previous level"
    exact hnp hp
  }

Conclusion 
"
In the next level, we will explore what it means to have proven `False`(pretty bad, or pretty good depending on how you look at it).
"

/- Use these commands to add items to the game's inventory. -/

NewTactic unfold
-- NewTheorem Nat.add_comm Nat.add_assoc

--DefinitionDoc Not as "¬" 
NewDefinition Not  
--TheoremDoc mul_left_cancel as "mul_left_cancel" in "*"
