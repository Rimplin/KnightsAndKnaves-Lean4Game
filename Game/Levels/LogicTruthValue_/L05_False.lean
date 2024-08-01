import Game.Metadata


World "Logic" 
Level 5

Title "asdf" 

Introduction 
"
# Truth Table
We want an operator which flips the value of a proposition `P`. Lets call this operator `Not` represented as `¬`. In other words, if `P` were true then `¬P` would be false and vice versa. 
Note that `¬P` is also a proposition, so `¬ (¬P)` is a valid expression.


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

# Natural Language Example
Let `P` denote the assertion 'Today is Monday'. `¬P` would then denote the assertion 'Today is not Monday'. You could also say that `¬P` denotes 'Today is Tuesday or Wednsday or Thursday or Friday or Saturday or Sunday'. Both assertions express the same thing (assuming there are 7 days of the week and these are their names) so either one is acceptable.

# Contradictions
Now we can construct propositional statements that are always false regardless of the values of their propositional variables. Having such a statement in your proof state would allow you to construct a term of type `False`. 

Such a statement is called a contradiction and is equal to `False` regardless of the proof state. Moreover, it is not something we assume to be true but something that is always true.
--------------------------------
# Defining `¬`

## But what is `False` exactly?(now we know what `False` is from the truth value perspective so this would need a rewrite in logic world).
For now, just know that `False` is a type that has no introduction rule and that proving `False` means deriving a contradiction. So, to prove `¬p` , you must assume `p` and derive a contradiction. We will explain in more detail what is meant by 'contradiction'.

To emphasize the fact that negation is an implication, you have to go through this simple level.
"
#check false_ne_true
#check False
variable {p : Prop}
variable {emTruth : (P : Prop) → P = True ∨ P = False}
-- type
-- ∀ {p : Prop}, p = True → p = False → False
example (hp:p=True) (hnp:p=False) (hnnp:¬p=True) (h' : (p = True) → (False = True) ) : False := by 

{
  #check hnnp
  unfold Not at hnnp
  have : (p=True) ∧ (p=False) := by exact And.intro hp hnp
  have this2: False :=by exact hnnp hp
  -- true regardless of proof state i.e true in every proof state, introduce it in a previous level and then when i come here, i can form the term on the left and rewrite to get `False`.
  #check this
  have this2: p ≠ True := by rw [hnp]; apply false_ne_true
  exact this2 hp
  
}
Statement (hp:p=True) (hnp:p=False)
  :  False := by

  {
    -- We can use the definition of `¬` to rewrite `hnp` as `p → False`
    -- This is the same as saying that we have a proof of `p` and we want to prove `False`
    -- So, we can use `hp` to prove `False`
    Hint (hidden:=true) "If you feel like seeing the implication definition of ¬ in the proof state would provide more clarity and make it easier to solve upcoming problems, you can always unfold ¬ to its implication form. Try `unfold Not at hnp`."
    --unfold Not at hnp 
    Hint "Now, this is just like the previous level"
    have : False=True := by rw [←hnp]; rw [←hp] 
    exact false_ne_true this

    --have : (False = True) = False := by {
    --  rw [this]
    --  
    --}
    --contradiction
    --exact hnp hp
  }

Conclusion 
"
In the next level, we will explore what it means to have proven `False`(pretty bad, or pretty good depending on how you look at it).
"

/- Use these commands to add items to the game's inventory. -/

NewTactic unfold
-- NewTheorem Nat.add_comm Nat.add_assoc

DefinitionDoc Not as "¬" 
NewDefinition Not  
--TheoremDoc mul_left_cancel as "mul_left_cancel" in "*"
