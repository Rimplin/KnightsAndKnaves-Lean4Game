import Game.Metadata

World "LogicTruthValue_" 
Level 7

Title "asdf" 

Introduction 
"
We proved `False`, what does this mean? What can we conclude? What does `False` IMPLY?
Let's check the `→` truth table:
truthtable

$$
\\begin{array}{|c|c|c|} 
\\hline
P & Q & P → Q \\\\
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
$$

-- Also we can make the user prove the principle of explosion using modus ponens. `False → Q` is true, modus ponens gives `Q` which is anything.
Let's focus on part of the truth table where `P` is `False`, because we want to see what `False` implies.
$$
\\begin{array}{|c|c|c|} 
\\hline
Q & False → Q \\\\
\\hline
T & T \\\\
\\hline
F & T \\\\
\\hline
\\end{array}
$$

# consequence of proving false
we have that the implication `False → Q` is true regardless what `Q` represents and regardless whether `Q` is true or is false. 
So `False` implies any proposition. This principle is known as: From contradiction anything follows.
It represents a contradiction. `False` elimination rule, `False.rec`,
expresses the fact that anything follows from a contradiction.
This rule is sometimes called ex falso (short for ex falso sequitur quodlibet),
or the principle of explosion.
For more information: [Propositional Logic](https://lean-lang.org/theorem_proving_in_lean4/propositions_and_proofs.html#propositional-logic)

## bad consequence, the system is worthless
So this is pretty good because now you can effortlessly prove anything you want!!!!! But this is also pretty bad because you can't really trust any of the results you obtain within an inconsistent system, can you?

In other words, within this proof state, all propositions are true. This is obviously absurd because it would mean for every proposition `p`, `p` is true and also `¬p` is true.

----

-- the following uses the definition of ¬ as an implication, so it doesn't avoid it. it can't be avoided
`False` is an 'empty' type that has no introduction rule. Then how can we prove `False`? Now explain negation and stuff.... We know that `False ≠ True` and its proof in Lean is:
```
false_ne_true : False ≠ True
```
i.e ¬(False = True) which is read as: 'it is not the case that `False = True`'.
In this proof state, we can prove that `False = True`. Replace the `p` in `hp` by `False` using `hnp`.

`False` is the empty proposition. Thus, it has no introduction rules.

Proving `False` means deriving a contradiction. So, to prove `¬p` , you must assume `p` and derive a contradiction. We will explain in more detail what is meant by 'contradiction'.
----------------------------

# Truth Table

# Natural Language Example
Let `P` denote the assertion 'Today is Monday'. `¬P` would then denote the assertion 'Today is not Monday'. You could also say that `¬P` denotes 'Today is Tuesday or Wednsday or Thursday or Friday or Saturday or Sunday'. Both assertions express the same thing (assuming there are 7 days of the week and these are their names) so either one is acceptable.

# Contradictions
Now we can construct propositional statements that are always false regardless of the values of their propositional variables. Having such a statement in your proof state would allow you to construct a term of type `False`. 

Such a statement is called a contradiction and is equal to `False` regardless of the proof state. Moreover, it is not something we assume to be true but something that is always true.
--------------------------------
"

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

NewTactic unfold rcases
NewTheorem false_ne_true 

NewDefinition Not  
