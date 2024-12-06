import Game.Metadata

World "LogicTruthValue_" 
Level 3 

Title "Or, `∨`" 

#check or_not_of_imp
#check imp_iff_not_or
Introduction 
"
In this level, we introduce the `∨` logical connective read as 'or'.

Its truth table is as follows:
$
\\begin{array}{|c|c|c|} 
\\hline
P & Q & P ∨ Q \\\\
\\hline
T & T & T \\\\
\\hline
T & F & T \\\\
\\hline
F & T & T \\\\
\\hline
F & F & F \\\\
\\hline
\\end{array}
$

From this truthtable, we conclude that to prove `P ∨ Q`,  we need either `P` being true or `Q` being true or both.

You can tell Lean which side of `∨` you want to prove by simply executing `left` or `right`.

In our case, we know the left side of `∨` is true, so use `left`.
"

/-

------------
The `∨` introduction rule works as described above:

The goal involves `∨`, and so (similar to `∧`) we need to use an introduction rule. Specifically, the `Or` introduction rule.
There are two `∨` introduction rules: 
Or.intro_left {a : Prop} (b : Prop) (h : a) : a ∨ b

Curly braces are for implicit arguments that you don't have to enter, paranthesis are for explicit ones you have to enter. What this theorem means is that you enter the proposition you want to the right of `∨` and a proof of the proposition you want on the left. In other words, proving a proposition gives you `that prop ∨ anything you want`......

```
Or.intro_left (b : Prop) (h : a) : a ∨ b
```
- `Or.intro_right`
```
Or.intro_right (a : Prop) (h : b) : a ∨ b
```

Pick the appropriate one.
-/
-- left, apply Or.inl are the same thing.

#check Or.inl
#check Or.intro_right
Statement (hP : P)  
  : P ∨ Q  := by
{
/-
```lean
Or.intro_left {a : Prop} (b : Prop) (h : a) : a ∨ b
```
***
Alias for `Or.inl`. 
***
-/
      left
      Hint "We have a proof that `P` is true, and we want to prove `P`"
      assumption
 --   exact Or.intro_left Q hP
/-
```lean
Or.inl {a b : Prop} (h : a) : a ∨ b
```
***
`Or.inl` is "left injection" into an `Or`. If `h : a` then `Or.inl h : a ∨ b`. 
***
-/
}

Conclusion 
"
"
/-
Notice that in the type of `Or.intro_left`, you need to explicitly give the type that will be used to the right of the `∨` but you don't need to do this for the type to the left of `∨`. How does Lean what to do? Well, the type of `Or.intro_left` is in fact:
```
Or.intro_left {a : Prop} (b : Prop) (h : a) : a ∨ b
```
The only difference is the curly braces. This means that `a` is an implicit argument. In other words, you don't need to give it explicitly, Lean will deduce it from the type of `h`. For example, if `h:P` where `P:Prop` then Lean will know that `a` is `P` and will put `P` to the left of `∨`.

A similar explanation applies to `Or.intro_right` which has the type:
```
Or.intro_right {b : Prop} (a : Prop) (h : b) : a ∨ b
```

You can avoid entering both `a` or `b` explicitly and instead use: 
```
Or.inl {a b : Prop} (h : a) : a ∨ b
Or.inr {a b : Prop} (h : b) : a ∨ b
```
-/
NewTheorem Or.inl Or.intro_left Or.intro_right Or.inr
NewTactic left assumption
