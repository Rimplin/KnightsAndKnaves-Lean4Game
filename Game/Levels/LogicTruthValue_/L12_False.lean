import Game.Metadata

World "LogicTruthValue_"
Level 7

Title "From `False`, anything follows."

--This principle asserts that if you have contradictory assumptions then you can prove anything.
--Example of contradictory assumptions:
--```
--h: P
--nh: ¬P
--```
-- principle of explosion
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
So `False` implies any proposition. This principle is known as: 'From `False` anything follows'.

Use this implication to prove `Q` where `Q` is any proposition.
"

Statement {Q : Prop} (h : False → Q) (hF : False) : Q := by 
  exact h hF

example : False → Q := by 
  #check False.elim
  intro h
  exact False.elim h

example (h : ∀(Q : Prop), False → Q) (hF : False) : x=2 := by 
  exact h (x=2) hF 

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
  -- explanation that False=True, how could this be etc...
  exact false_ne_true hp
example (hp:p=True) (hnp:p=False)
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
Having proven `False`, instead of going through this to prove `Q` you can use the the `contradiction` tactic. If you were able to prove `False`, then the `contradiction` tactic will prove the goal regardless of what the goal because 'from `False`, anything follows'.
"
-- absurdity of having `False` proven. inconsistent system
-- If you were able to find `h:False` i.e prove `False` then our system is worthless because we can prove anything. To reiterate, such a system would be called an inconsistent system because of a contradiction.
--the basic idea is that if you have in your proof state an `h` such that `h:False` then you can prove any proposition you want. In other words, within this proof state, all propositions are true. This is obviously absurd because it would mean for every proposition `p`, `p` is true and also `¬p` is true.

NewTactic «have» unfold rcases contradiction
NewTheorem false_ne_true 

NewDefinition False Not
