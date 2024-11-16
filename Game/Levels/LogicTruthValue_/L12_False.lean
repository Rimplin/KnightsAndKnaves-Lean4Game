import Game.Metadata

World "LogicTruthValue_" 
Level 7

Title "asdf" 

Introduction 
"
We proved `False`, what does this mean? What can we conclude? What does `False` IMPLY?

Let's check the `→` truth table:
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

We have that the implication `False → Q` is true regardless what `Q` represents and regardless whether `Q` is true or is false. 
So `False` implies any proposition. This principle is known as: From contradiction anything follows.

The tactic to achieve this is `contradiction`.
Having a proof of `False`, the `contradiction` tactic will always close the goal.
"

#check false_ne_true
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
Such a system having `False` or a contradiction is called an inconsistent system.
The consequence of having `False` is the following. 

Any proposition is true and studying the current system becomes worthless.
"

NewTactic unfold rcases contradiction
NewTheorem false_ne_true 

NewDefinition Not
