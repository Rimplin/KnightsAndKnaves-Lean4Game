import Game.Metadata

/--
Unfoldable:
unfold Not at ...
¬P is P → False

$
\begin{array}{|c c|c|} 
\hline
P & ¬P \\
\hline
T & F \\
F & T \\
\hline
\end{array}
$
-/
DefinitionDoc Not as "¬"

/--
You can think of a proposition as a statement that is either true or false(obviously, it can't be both at the same time).

For an object of type P where P is of type Prop, i.e `h : P` where `P : Prop`, `h` would be a proof or a witness that `P` is true. Equivalently, from `h` we can construct a term `h' := eq_true h of type `h' : P = True` which would be a proof that P is true as well. Both perspectives are interchangeable and equivalent.

# Constructing new propositions from old ones
The atomic propositions in the compound proposition `p ∧ q` are : `p`, `q`. Of course, `p ∧ q` can be used to construct more complicated propositions.



## Connecting Propositions With A Logical Connective
It is important to note that connecting two proposition via a logic connective results in a proposition as well. If this wasn't the case, then how could we talk about the truth value of `P ∧ Q` if `P ∧ Q` were not a proposition! This proposition constructed using a logical connective and other propositions, like any other proposition, has a truth value. This truth value depends on the truth value of the propositions it was built out of and the rules of the logical connective. This is clearly illustrated in a truth table. 


# Truth table
The truth table of a logical connective illustrates the rule for that logical connective , i.e the truth value of the compound statement depending on the truth value of the propositions it connects.

-/
DefinitionDoc «Prop» as "Prop"


/-- 
# truth table
$
\begin{array}{|c|c|c|} 
\hline
P & Q & P → Q \\
\hline
T & T & T \\
\hline
T & F & F \\\\
\hline
F & T & T \\\\
\hline
F & F & T \\\\
\hline
\end{array}
$
-/
DefinitionDoc imp as "→"

/--

`And.intro` takes a proof of `P`, a proof of `Q`, and transforms/evaulates them to a proof of `P ∧ Q` where `P Q : Prop`.

Truth table:

$
\begin{array}{|c|c|c|} 
\hline
P & Q & P ∧ Q \\
\hline
T & T & T \\
\hline
T & F & F \\
\hline
F & T & T \\
\hline
F & F & T \\
\hline
\end{array}
$
-/
DefinitionDoc and as "∧" 

/--
`rfl` is short for reflexivity. In the context of numbers, it is the property that for any number `a`, `a = a`.

More generally, the `rfl` tactic will close all goals of the form `X=X`, regardless of what `X` is, `X=Y` where `X` and `Y` are identical. rfl can also prove the equality of two things that are 'equal by definition'.

In fact, `rfl` is not a tactic but syntactic sugar for `exact rfl`. `rfl` is of type `a = a` for any `a`.



`rfl` also applies more generally, `rfl` will close any goal of the form `A=B` where `A`,`B` are identical. If needed, `rfl` will unfold both sides into their definitions and then check if they are equal. In other words, `rfl` can prove the equality of two things that are 'equal by definition'.
## examples
```
x - 7 = x - 7
```
`rfl` will close this goal.
-/
TacticDoc rfl

/--
testing stuff, does importing work?!?!?!?!
-/
TacticDoc left



/--
[[mathlib_doc]]
There is an alternative syntax for `have` which you can view in the right side pane. In any case, it will be introduced later on when its more convenient to use.
`have name := ........`
-/
TacticDoc «have»



/--
## Overview
Having h : P and P as your goal, exact h will close the goal. exact h asserts that h is exactly whats needed to prove the goal which makes sense because h is a proof of P.(It doesn't matter what P is)
-/
TacticDoc exact


/-- 
Normalize numerical expressions. Supports the operations `+` `-` `*` `/` `⁻¹` `^` and `%`
over numerical types such as `ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ`.

-/
TacticDoc norm_num
/--
```
`have name-of-object : type := by ...` 
```
where `...` is the proof.
`name-of-object` can be whatever you want, leaving it empty would  give the theorem a name automatically. The `type` in this case is the statement we want to prove. 
-/
TacticDoc «have» 
/--

# Truth table
The truth table of a logical connective illustrates the rule for that logical connective , i.e the truth value of the compound statement depending on the truth value of the propositions it connects.
The following truth table illustrates this for the previously discussed `∧` connective.
`T` stands for true
`F` stands for false
$
\begin{array}{|c c|c|} 
\hline
P & Q & P ∧ Q \\
\hline
T & T & T \\
T & F & F \\
F & T & F \\
F & F & F \\
\hline
\end{array}
$
Notice that `P ∧ Q` is true when both `P` is true and `Q` is true, being false otherwise.
-/
TheoremDoc And as "And" in "Logic"

/--
A summary of all the terminology presented throughout the game, in order of appearance.

-
-/
DefinitionDoc Terminology as "Terminology"


