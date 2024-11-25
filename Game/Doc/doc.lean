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

Notice that this definition is an implication and that the truth table with `¬P` and the truth table with `P → False` are identical.

What this means is that to prove `¬P`, we assume `P` and derive a contradiction i.e constructing an object of type `False`. 
In other words, having `¬P` as a goal, you have to start the proof with `intro` because you are proving an implication.

It represents a contradiction. `False` elimination rule, `False.rec`,
expresses the fact that anything follows from a contradiction.
This rule is sometimes called ex falso (short for ex falso sequitur quodlibet),
or the principle of explosion.
For more information: [Propositional Logic](https://lean-lang.org/theorem_proving_in_lean4/propositions_and_proofs.html#propositional-logic)

`False` is an 'empty' type that has no introduction rule. 

`False` is the empty proposition. Thus, it has no introduction rules.

Proving `False` means deriving a contradiction. So, to prove `¬p` , you must assume `p` and derive a contradiction. 
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
`∩` is an operator on sets.

Applying it to two sets `A`,`B`:
```
A ∩ B
```

`A ∩ B` is itself another set, containing elements that are in both `A` and `B`.

`A ∩ B = ∅` means that `A` and `B` have no common element i.e no element of `A` belongs to both and no element of `B` belongs to both.
-/
DefinitionDoc inter as "∩"

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
Given the following:
```
Assumptions:
h : A = B

Goal:
some expression involving A
```

`rw [h]` would change the goal by replacing every occurrence of `A` with `B`.

By default, rw uses an equation in the forward direction, matching the left-hand side of the equation with an occurrence of that in the goal, and replaces it with the right-hand side. 

The notation ←t can be used to instruct the tactic to use the equality t in the reverse direction.
-/
TacticDoc rw

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

This is done by `exact h`.
-/
TacticDoc exact

/--
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
Another way to express this is that you have two possibilities one of which(or both) is supposed to be true, and you know its definitely not the second option. All is left is the first option. 

Given the statement, its either 'this' or 'that'. If we know its not 'that' then its definitely 'this'.
-/
TheoremDoc notright_left as "notright_left" in "Logic"

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
The set `Knight` would be the set of inhabitants of the island that are knights i.e satisfying the property of always telling the truth, the set `Knave` being the set of inhabitants of the island that are knives i.e the ones that always lie. 

## In Lean
```
Set K
```

```
Finset K
```
-/
DefinitionDoc Finset as "Finset"

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
Knight version...
Given inhabitant `A`:

The translation we use is based on the following:
- If `A` is a knight, then `A`'s statement is true.
- If `A`'s statement is true, then `A` is a knight.

Formally:
```
A ∈ Knight → stA
stA → A ∈ Knight
```

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
A ∈ Knight ↔ B ∈ Knave
```

### equivalent translations, using knaves
Given inhabitant `A`:

The translation we use is based on the following:
- If `A` is a knave, then `A`'s statement is false, i.e its negation is true.
- If `A`'s statement is false, then `A` is a knave.

Formally:
```
A ∈ Knave → ¬stA
¬stA → A ∈ Knave
```

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
A ∈ Knave ↔ ¬(B ∈ Knave)
```
-/
DefinitionDoc KnightsKnaves as "Knights and Knaves"

--# Xor
--To introduce Xor, introduce as the negation of if and only if. Xor is inequivalence, Xor is such that exactly one of the propositions is truei.e exclusive or. 
--
--def Xor' (a b : Prop) := (a ∧ ¬ b) ∨ (b ∧ ¬ a)
--
--# Exclusive Or 
--
--## Rewriting Xor'
--`Xor' p q` can be rewritten as:
--```
--(p ∧ ¬q) ∨ (¬p ∧ q)
--```
--To rewrite `Xor'` in the goal:
--```
--rw [Xor']
--```
--
--To rewrite `Xor'` in hypothesis `h`:
--```
--rw [Xor'] at h
--```
---/
--DefinitionDoc Xor' as "Xor'" 
--NewDefinition Xor' 

DefinitionDoc Nat as "ℕ"  


/--
### **Logic Constants & Operators**
### **Equational Reasoning**
| $Name~~~$ | $Ascii~~~$ | $Unicode$ | $Unicode Cmd$ |
| --- | :---: | :---: | --- |
|     |       |       | `mul_left_cancel\0`|
| True | `True` |  |  |
| False | `False` |  |  |
| Not | `Not` | ¬ | `\n` `\not` `\neg` `\lnot` |
| And | `/\` | ∧ | `\and` `\an` `\wedge` |
| Or | `\/` | ∨ | `\v` `\or` `\vee` |
| Implies | `->` | → | `\r` `\imp` `\->` `\to` `\r-` `\rightarrow` |
| Iff | `<->` | ↔ | `\iff` `\lr-` `\lr` `\<->` `\leftrightarrow` |
| For All | `foral` | ∀ | `\all` `\forall` |
| Exists | `exists` | ∃ | `\ex` `\exists` |

### **Other Unicode**
| $Name$ | $Unicode~~~$ | $Unicode Cmd$ |
| --- | :---: | --- |
| Angle brackets | ⟨ ⟩ | `\<` `\>` `\langle` `\rangle` |
| Subscript Numbers | ₁ ₂ ₃ ... | `\1` `\2` `\3` ... |
| Left Arrow | ← | `\l` `\leftarrow` `\gets` `\<-` |
| Turnstyle | ⊢ | `\│-` `\entails` `\vdash` `\goal` |

$
\begin{array}{|c|c|} 
\hline
Unicode & Text \\
\hline
\text{mul\_left\_cancel₀} & `mul\_left\_cancel\0` \\
\hline
\end{array}
$
mul_left_cancel₀ written as mul_left_cancel\0
-/
DefinitionDoc UnicodeSymbols as "Unicode Symbols"

/-- [[mathlib_doc]] -/
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
