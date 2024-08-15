import Game.Metadata

World "LogicTruthValue_" 
Level 12

Title "asdf" 

Introduction 
"
Our goal is to prove `False`. This looks problematic from the get go, and we will go into the details of that in this level. But, let's first go discuss what `False` is as a type.


`False` is an 'empty' type that has no introduction rule. Then how can we prove `False`? Now explain negation and stuff.... We know that `False ≠ True` and its proof in Lean is:
```
false_ne_true : False ≠ True
```
i.e ¬(False = True) which is read as: 'it is not the case that `False = True`'.
In this proof state, we can prove that `False = True`. Replace the `p` in `hp` by `False` using `hnp`.


`False` is the empty proposition. Thus, it has no introduction rules.
It represents a contradiction. `False` elimination rule, `False.rec`,
expresses the fact that anything follows from a contradiction.
This rule is sometimes called ex falso (short for ex falso sequitur quodlibet),
or the principle of explosion.
For more information: [Propositional Logic](https://lean-lang.org/theorem_proving_in_lean4/propositions_and_proofs.html#propositional-logic)

Proving `False` means deriving a contradiction. So, to prove `¬p` , you must assume `p` and derive a contradiction. We will explain in more detail what is meant by 'contradiction'.
----------------------------
# Truth Table
We want an operator which flips the value of a proposition `P`. Lets call this operator `Not` represented as `¬`. In other words, if `P` were true then `¬P` would be false and vice versa. 
Note that `¬P` is also a proposition, so `¬ (¬P)` is a valid expression. Moreover, `¬ (¬P)` is a proposition so `¬ (¬ (¬P))` or `¬¬¬P` is a valid expression (and so on).


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
Notice that this definition is an implication which you have learned to deal with in the previous level and that the truth table with `¬P` and the truth table with `P → False` are identical which means that the implication definition captures what we want `¬` to mean.

# Natural Language Example
Let `P` denote the assertion 'Today is Monday'. `¬P` would then denote the assertion 'Today is not Monday'. You could also say that `¬P` denotes 'Today is Tuesday or Wednsday or Thursday or Friday or Saturday or Sunday'. Both assertions express the same thing (assuming there are 7 days of the week and these are their names) so either one is acceptable.

# Contradictions
Now we can construct propositional statements that are always false regardless of the values of their propositional variables. Having such a statement in your proof state would allow you to construct a term of type `False`. 

Such a statement is called a contradiction and is equal to `False` regardless of the proof state. Moreover, it is not something we assume to be true but something that is always true.
--------------------------------
# Defining `¬`

## But what is `False` exactly?(now we know what `False` is from the truth value perspective so this would need a rewrite in logic world, no it doesn't because we were dealing with `= False` but now we are dealing with `→ False`).
For now, just know that `False` is a type that has no introduction rule and that proving `False` means deriving a contradiction. So, to prove `¬p` , you must assume `p` and derive a contradiction. We will explain in more detail what is meant by 'contradiction'.

To emphasize the fact that negation is an implication, you have to go through this simple level.
"
-- : False = True

example (hnp:p=False) (hp:p=True) (hnnp:¬p=True) (h' : (p = True)) : False    := by 
  Hint 
  "
  Since `p=False` and `p=True`, then `False` and `True` must be the same thing right? (i.e equal). Produce a `False = True`.
  "
  rw [hnp] at hp
  Hint 
  -- prove ¬(P ∧ ¬P)
  "
   
So, we have that `p is the case` and that `p is not the case` where `p` denotes `False = True`. How can this be?
 So, is it both at the same time? For the world we live in, this wouldn't make much sense. This is like saying the door is open and closed at the same time. Or saying I am sick and I am not sick. For our world, asserting `P ∧ ¬P` for any proposition `P` is really weird. We say that `P` and `¬P` contradict each either, or that they are contradictory. And we say that proving `P ∧ ¬P`,`False`, or any other statement that is always `False` is deriving contradiction
 Ok... this one is going to be an exception, put the manipulation perspective first to define ¬ and show the truth table of ¬ and talk (maybe) a bit about False then put this level and talk about the rest of false....

Put truth table of `P ∧ ¬P` now?
-------------------
   We know that `False` does not equal `True` but we were able to prove this. 
  "
  -- assumption
  -- explanation that False=True, how could this be etc...
  exact false_ne_true hp
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
NewTheorem false_ne_true

DefinitionDoc Not as "¬" 
NewDefinition Not  
--TheoremDoc mul_left_cancel as "mul_left_cancel" in "*"
