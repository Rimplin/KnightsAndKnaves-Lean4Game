import Game.Metadata

/--
## Implication defintion
`¬P` is equivalent to `P → False`

Given
```
hnP : ¬P
```
unfold Not at hnP will result in:
```
hnP : P → False
```

## truth table
$
\begin{array}{|c c|} 
\hline
P & ¬P \\
\hline
T & F \\
F & T \\
\hline
\end{array}
$

Notice that this definition is an implication and that the truth table with `¬P` and the truth table with `P → False` are identical.

What this means is that to prove `¬P`, we assume `P` and derive a contradiction i.e constructing an object of type `False`. 
In other words, having `¬P` as a goal, you have to start the proof with `intro` because you are proving an implication.
-/
DefinitionDoc Not as "¬"

/--
Proving `False` means deriving a contradiction.

A contradiction is when `P` and `¬P` are both true. We say that `P` and `¬P` contradict each other.

# Principle of explosion, from `False` anything follows.
This principle asserts that if you have contradictory assumptions then you can prove anything.
```
hP: P
hnP: ¬P
```
Since `hnP : ¬P` is `P → False` , we can obtain `hnP hP : False`.

Moreover, we know that `hFQ : False → Q` for any `Q : Prop` and so `hFQ (hnP hP) : Q`. (using `contradiction` after having proven `False` will close any goal as well)
-/
DefinitionDoc False as "`False`"

/--
You can think of a proposition as a statement that is either true or false(obviously, it can't be both at the same time).

Moreover, these statements are denoted by a symbol like `P`,`Q`,`R`.

For an object of type `P` where `P` is of type Prop, i.e `h : P` where `P : Prop`, `h` would be a proof or a witness that `P` is true.

# Constructing new propositions from old ones
The atomic propositions in the compound proposition `p ∧ q` are : `p`, `q`. Of course, `p ∧ q` can be used to construct more complicated propositions.

## Connecting Propositions With A Logical Connective
This truth value depends on the truth value of the propositions it was built out of and the rules of the logical connective. This is clearly illustrated in a truth table. 

# Truth table
The truth table of a logical connective illustrates the rule for that logical connective , i.e the truth value of the compound statement depending on the truth value of the propositions it connects.

-/
DefinitionDoc «Prop» as "Prop"

/--
Logical implication `P → Q` is made up of two components:
- The premise, which in this case is `P`
- The conclusion, which in this case is `Q`

P → Q is read as 'If P is true, then Q is true.

# truth table
$
\begin{array}{|c c|c|} 
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

A statement `P → Q` is false when `P` is true and `Q` false, it's true otherwise.

# Implication as a function
What logical implication does is that it takes evidence or proof for `P` and transforms it returning a proof of `Q`.
The truth of `P` IMPLIES the truth of `Q`. A proof of `P` IMPLIES a proof of `Q`.

In other words, it acts like a function. If you give `P → Q` a proof of `P`, you get a proof of `Q`.
-/
DefinitionDoc imp as "→"

/--
Truth table:

$
\begin{array}{|c c|c|} 
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
DefinitionDoc and as "∧" 

/--
# Truth Table
$
\begin{array}{|c c|c|} 
\hline
P & Q & P ∨ Q \\
\hline
T & T & T \\
\hline
T & F & T \\
\hline
F & T & T \\
\hline
F & F & F \\
\hline
\end{array}
$

From the truth table, we can see that if one of `P`,`Q` is true then `P ∨ Q` is true. 

Therefore, if we have `P ∨ Q` as our goal, it is enough to prove `P` or to prove `Q`.

Having `P ∨ Q` as the goal, you can tell Lean that you want to prove the left side by simply typing `left` or the right side by simply typing `right`.
-/
DefinitionDoc or as "∨"

/--
`∩` is an operator on sets.

Applying it to two sets `A`,`B`:
```
A ∩ B
```

`A ∩ B` is itself another set, containing elements that are in both `A` and `B`.
In other words, `x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B`.

`A ∩ B = ∅` means that `A` and `B` have no common element i.e no element of `A` belongs to both and no element of `B` belongs to both.
In other words, `x ∈ A → x ∉ B` , `x ∈ B → x ∉ A` which are `inleft_notinright` and `inright_notinleft` respectively.
-/
DefinitionDoc inter as "∩"

/--
`rfl` is short for reflexivity. In the context of numbers, it is the property that for any number `a`, `a = a`.

`rfl` also applies more generally, `rfl` will close any goal of the form `A=B` where `A`,`B` are identical. If needed, `rfl` will unfold both sides into their definitions and then check if they are equal. In other words, `rfl` can prove the equality of two things that are 'equal by definition'.

In fact, `rfl` is not a tactic but syntactic sugar for `exact rfl`. `rfl` is of type `a = a` for any `a`.

## examples
```
x - 7 = x - 7
```
`rfl` will close this goal.
-/
TacticDoc rfl

/--
The assumption tactic searches for an assumption that matches the goal, and closes the goal if it finds one.

Given,
```
Objects
P : Prop

Assumptions
hP : P

Goal
P
```
`assumption` will close the goal.
-/
TacticDoc assumption

/--
Given,
```
PorQ : P ∨ Q

Goal
some-goal
```
`cases PorQ` will first assume `P` and ask you to prove `some-goal` and then it will assume `Q` and ask you to prove `some-goal`. So in both cases, `some-goal` is true. Therefore we can conclude `some-goal`. This is called a proof by cases.
-/
TacticDoc cases
/--
`intro` tactic is used to deal with goals of the form `P → Q`.

Having the following:
```
Goal:
P → Q
```
We want to prove that 'If `P` is true, then `Q` is true'. 

To do this, we first need to assume `P` then prove `Q`. Assuming `P` is done using `intro name` for any 'name'.
-/
TacticDoc intro

/--
The `constructor` tactic will split a goal of the form `P ∧ Q` into two subgoals `P`,`Q` where you can deal with each one separately.
-/
TacticDoc constructor

/--
Contradiction is a tactic that detects if you have contradictory assumptions and if so, closes the goal.

Having
```
h : False
```
or
```
hP : P 
hnP : ¬P
```
(or other 'simple' contradictions)
`contradiction` will close any goal.
-/
TacticDoc contradiction

/--
Given the following:
```
Assumptions:
h : A = B

Goal:
some expression involving A
```

`rw [h]` would change the goal by replacing every occurrence of `A` with `B`.

By default, rw uses an equation in the forward direction, matching the left-hand side of the equation `h` with an occurrence of `A` in the goal, and replaces it with the right-hand side i.e `B`. 

The notation `rw [←h]` can be used to instruct the tactic to use the equality `h` in the reverse direction i.e replace an occurrence of `B` with `A`.

## Behavior with `=` and `↔`
For `rw [h]`, the behavior is exactly the same for both, whether you had `h : x=2` or `h : P ↔ Q`.
-/
TacticDoc rw

/--
Having the goal of the form:
```
P ∨ Q
```
for `P Q : Prop`, `left` transforms the goal to `P`.
-/
TacticDoc left

/--
Having the goal of the form:
```
P ∨ Q
```
for `P Q : Prop`, `right` transforms the goal to `Q`.
-/
TacticDoc right

/--

## Syntax

### without specifying the type
`have name := some-term `
where `name` is the new assumption that will appear which will have `some-type` where `some-term : some-type` and `some-type : Prop` i.e `some-term` is a proof of some proposition.

### with specifying the type
```
have name : some-proposition := by
  proof steps
  ...
  proof steps
```
You would need to use editor mode if there are multiple proof steps.

Inside the have block, you would have a new goal which is `some-proposition` say `x=2` , `A ∈ Knight` etc...

Not specifying the `type` when using `have` doesn't allow you to use tactics.

## Examples

Given the following assumptions from lemmas world, level 1:
```
Assumptions:
Aleft : A ∈ left 
Aright : A ∈ right 
h: left ∩ right = ∅
AinBothInter: A ∈ left ∧ A ∈ right → A ∈ left ∩ right
```

### without specifying the type
`have AinBoth := AinBothInter (And.intro Aleft Aright)` will add the following to the assumptions:
```
AinBoth : A ∈ left ∩ right
```

### specifying the type
`have  AinBoth : A ∈ left ∩ right := by AinBothInter (And.intro Aleft Aright)` will add the following to the assumptions in the proof state:
```
AinBoth : A ∈ left ∩ right
```
-/
TacticDoc «have»

/--
`And.intro` takes a proof of `P`, a proof of `Q`, and gives a proof of `P ∧ Q` where `P Q : Prop`.

Given,
```
hP : P
hQ : Q
```
we have `And.intro hP hQ : P ∧ Q`
-/
TheoremDoc And.intro as "And.intro" in "And"

/--
Refer to `Prop` documentation if you need to.

## Overview
For the following proof state:
```
Objects
P : Prop

Assumptions
hP : P

Goal:
P
```
Remember that `hP : P` where `P : Prop` means `hP` is a proof of `P`.

Since the goal is to prove `P`, the only thing we have to do is to let Lean know that we do have such a proof. In other words, `hP` is EXACTLY whats needd to prove the goal. The type of `hP` EXACTLY matches the goal.

exact h asserts that h is exactly whats needed to prove the goal which makes sense because h is a proof of P.(It doesn't matter what P is)
This is done by `exact h`.
-/
TacticDoc exact

/--
Here we introduce the `have` tactic which allows us to add theorems to the context(which you would have to prove, of course). 

```
`have name-of-object : type := by ...` 
```
where `...` is the proof.
`name-of-object` can be whatever you want, leaving it empty would  give the theorem a name automatically. The `type` in this case is the statement we want to prove. 
-/
TacticDoc «have» 

/--
The `contradiction` tactic works for the following proofs states:
```
h : False
```

```
hP : P
hnP : ¬P
```

and
```
hP : P
```
where Lean knows that `¬P` is true.

Example:
-- disjoint
You need to show that having two sets being disjoint (i.e sharing no common element) and having a common element is a contradiction.
-/
TacticDoc contradiction

/--

-/
TheoremDoc notleft_right as "notleft_right" in "Logic"

/--

-/
TheoremDoc four_pos as "four_pos" in "*"

/--
Another way to express this is that you have two possibilities one of which(or both) is supposed to be true, and you know its definitely not the second option. All is left is the first option. 

Given the statement, its either 'this' or 'that'. If we know its not 'that' then its definitely 'this'.
-/
TheoremDoc notright_left as "notright_left" in "Logic"

/--
```
theorem inleft_notinright
(h : left ∩ right = ∅ )
(Aleft : A ∈ left)
: A ∉ right
```

Given the following proof state:
```
Objects
A : Inhabitant
left right : Finset Inhabitant

Assumptions
h : left ∩ right = ∅
Aleft : A ∈ left

Goal
A ∉ right
```

exact `inleft_notinright h Aleft` will close the goal.
-/
TheoremDoc inleft_notinright as "inleft_notinright" in "Knights and Knaves"

/--
```
theorem disjoint
(h : left ∩ right = ∅ )
(Aleft : A ∈ left)
(Aright : A ∈ right)
: False
```

Given the following proof state:
```
Objects
A : Inhabitant
left right : Finset Inhabitant

Assumptions
h : left ∩ right = ∅ 
Aleft : A ∈ left
Aright : A ∈ right

Goal
False
```

`exact disjoint h Aleft Aright` will close the goal
-/
TheoremDoc disjoint as "disjoint" in "Knights and Knaves"

/--
A summary of all the terminology presented throughout the game, in order of appearance.

Theorems represent an implication say:
```
thm : P → Q
```

They work for `P`,`Q` of any type. What `thm` means is the following, give me an object of type `P` and i will return an object of type `Q`. 

Therefore, theorems expect arguments given in a specific order after which the obtained expression is an object which has the conclusion as its type.

For
```
thm : P → Q
hP : P
```
`(thm hP) : Q`

For the special case where `P : Prop`, `Q : Prop` ,the interpretation of `thm` is what implication in logic means.  

What `thm` means is the following, give me an object of type `P` which in this case is a proof of `P` and i will return an object of type `Q` which in this case is a proof of `Q`. 

In other words, `thm` means 'If P is true, then Q is true'.
-/
DefinitionDoc Terminology as "Terminology"

/--
## Definition
A set is a collection of 'entities' or 'objects' that satisfy a certain property. The objects in a set are called 'elements' of the set.

A finite set is a set with finitely many elements.

## Examples
The set `Knight` would be the set of inhabitants of the island that are knights i.e satisfying the property of always telling the truth, the set `Knave` being the set of inhabitants of the island that are knaves i.e the ones that always lie.

## In Lean

```
Set K
Set Inhabitant
```

```
Finset K
Finset Inhabitant
```
-/
DefinitionDoc Finset as "Finset"

/--
Given the following proof state:
```
left : Finset K
```

`A ∈ left` read as 'A in left'.

`A ∉ left` read as 'A not in left' means `¬(A ∈ left)` , `A ∈ left → False`.
-/
DefinitionDoc mem as "∈"

/--
## Objects

The objects involved are:
- of type inhabitant indicated by a capital letter
- the two finite sets `Knight` , `Knaves`.

As a proof state:
```
Objects
A : Inhabitant
B : Inhabitant 
C : Inhabitant
Knight : Finset Inhabitant
Knave : Finset Inhabitant
```
There will be at most three inhabitants in the puzzles for simplicity, but you can ofcourse have more.

## Assumptions
Knights tell the true and knaves lie. So no one can be both at the same time i.e `Knight ∩ Knave = ∅`

Moreover, every inhabitant is either a knight or a knave i.e `A ∈ Knight ∨ A ∈ Knave` for any `A : Inhabitant`.

As a proof state:
```
Assumptions:
h : Knight ∩ Knave = ∅ 
Or : A ∈ Knight ∨ A ∈ Knave
```

## Summary
Putting every together:
```
Objects
A : Inhabitant
B : Inhabitant 
C : Inhabitant
Knight : Finset Inhabitant
Knave : Finset Inhabitant

Assumptions
h : Knight ∩ Knave = ∅ 
Or : A ∈ Knight ∨ A ∈ Knave
```

## Translating statements to formal notation
Given an inhabitant `A`,

The translation we use is based on the following:
- If `A` is a knight, then `A`'s statement is true.
- If `A`'s statement is true, then `A` is telling the truth i.e is a knight.

Formally:
```
A ∈ Knight → statement-of-A
statement-of-A → A ∈ Knight
```
where `statement-of-A : Prop` represents `A`'s statement.

Combining them we get,
```
stA : A ∈ Knight ↔ statement-of-A
```

### Quick Example
If,
```
A says B is a knave
```

then,
```
A ∈ Knight → B ∈ Knave
B ∈ Knave → A ∈ Knight
```

Combining them using `↔`:
```
stA : A ∈ Knight ↔ B ∈ Knave
```

### equivalent translations, using knaves
Given inhabitant `A`,

The translation we use is based on the following:
- If `A` is a knave, then `A`'s statement is false, i.e its negation is true.
- If `A`'s statement is false, then `A` is lying i.e is a knave.

Formally:
```
A ∈ Knave → ¬statement-of-A
¬statement-of-A → A ∈ Knave
```
where `statement-of-A : Prop` represents `A`'s statement.

Combining them we get,
```
stAn : A ∈ Knave ↔ ¬statement-of-A
```

### Quick Example
If,
```
A says B is a knave
```

then,
```
A ∈ Knave → ¬(B ∈ Knave)
¬(B ∈ Knave) → A ∈ Knave
```

Combining them using `↔`:
```
stAn : A ∈ Knave ↔ ¬(B ∈ Knave)
```
-/
DefinitionDoc KnightsKnaves as "Knights and Knaves"

DefinitionDoc Nat as "ℕ"

/--
### **Logic Constants & Operators**
| $Name~~~$ | $Ascii~~~$ | $Unicode$ | $Unicode Cmd$ |
| --- | :---: | :---: | --- |
| True | `True` |  |  |
| False | `False` |  |  |
| Not | `Not` | ¬ |  `\not` `\neg`  |
| And | `/\` | ∧ | `\and`  |
| Or | `\/` | ∨ |  `\or`  |
| Implies | `->` | → |  `\imp` |
| Iff | `<->` | ↔ | `\iff` |

### **Other Unicode**
| $Name$ | $Unicode~~~$ | $Unicode Cmd$ |
| --- | :---: | --- |
| Angle brackets | ⟨⟩ | `\<>` |
| Left Arrow | ← | `\l` `\leftarrow` `\gets` `\<-` |

-/
DefinitionDoc UnicodeSymbols as "Unicode Symbols"

/--
`P ↔ Q`  is defined as `(P → Q) ∧ (Q → P)`. 

Its truth table looks like the folowing:
$
\begin{array}{|c c|c c|c|} 
\hline
P & Q & P → Q & Q → P & P → Q ∧ Q → P\\
\hline
T & T & T & T & T \\
\hline
T & F & F & T & F \\
\hline
F & T & T & F & F \\
\hline
F & F & T & T & T \\
\hline
\end{array}
$

So, `P ↔ Q` is true when `P,Q` are true or `P,Q` are false, i.e when `P` and `Q` have the same truth value. Therefore, `P` and `Q` are equivalent from a truth value perspective regardless what the statement of `P` and of `Q` is.

## Extracting Each Implication
```
h : P ↔ Q
h.mp : P → Q
h.mpr : Q → P
```
`h.mp` is the forward direction and `h.mpr` is the backward direction.

## `P ↔ Q` is `P = Q`
Since `P`, `Q` have the same truth value , they can be used interchangeably.
You can think of `P ↔ Q` as `P = Q` and use `rw` in the same way you would if there was an actual `=` in the expression.

For example:
```
h : P ↔ Q
hP : P
```
Doing `rw [h] at hP` results in:
```
h : P ↔ Q
hP : Q
```
-/
DefinitionDoc Iff as "↔"

/--

-/
TheoremDoc Nat.mul_left_cancel as "Nat.mul_left_cancel" in "*"

/--
As an implication
```
Knight ∩ Knave = ∅ →
A ∈ Knight ∨ A ∈ Knave →
(A ∈ Knight ↔ A ∈ Knave) → False
```
-/
TheoremDoc IamKnave as "IamKnave" in "Knights and Knaves"

/--
```
theorem inright_notinleft
(h : left ∩ right = ∅ )
(Aright : A ∈ right)
: A ∉ left
```

Given the following proof state:
```
Objects
A : Inhabitant
left right : Finset Inhabitant

Assumptions
h : left ∩ right = ∅
Aright : A ∈ right

Goal
A ∉ left
```

exact `inright_notinleft h Aright` will close the goal.
-/
TheoremDoc inright_notinleft as "inright_notinleft" in "Knights and Knaves"
