import Game.Metadata


World "EquationalReasoningCalc" 
Level 1

Title "" 

Introduction 
"
This world is just:
'
In Lean, an algebraic rearrangement is indicated by the tactic ring, and a substitution by the tactic rw (stands for “rewrite”). When making a substitution, you must indicate by name the hypotheses which you are substituting.
'
'create a term to deal with ...'

Notice that a proof completely made by rewrites can be done exactly the same way with and without `calc`.
Remember level 3 in equational reasoning.

# `calc`
`calc` is a tactic that supports forward reasoning. In other words, if the goal is of the form `x = y` then you start from `x` and you reason 'forward' until you reach `y` applying substitutions(rewrites) and manipulations of the expresison you have.

An example would definitely be enlightening, given the following problem:
```
example (a b : ℤ) (h : a - b = 0) : a = b := by
```

```
a b : ℤ
h : a - b = 0
⊢ a = b
```
Note: ℤ is the set of integers, ℤ = {...,-3,-2,-1,0,1,2,3,...}
This is what the solution would look like:
```
calc
  a = (a - b) + b := by ring
  _ = 0 + b := by rw [h]
  _ = b := by ring 
```
Notice that every step of the calculation is shown on each line and justified at the end of that line.
Lets go through this proof line by line.
First, we prove that `a = (a - b) + b` using the `ring` tactic.
Then, we prove that `(a - b) + b = 0 + b`, the `_` there is to avoid having to write `(a - b) + b` again, Lean would just deduce that. Since we know that `(a - b) = 0`, this step is justified by a rewrite.
Finally, we prove that `0 + b = b` using the ring tactic.
Now, what calc does is the following: 
since `a = (a - b) + b` and `(a - b) + b = 0 + b` then `a = 0 + b` and since `0 + b = b` then `a = b` which is the goal. This is whats known as the transitivity property of `=`:
If `a = b` and `b = c` then `a = c`.
This is obvious because you can substitue `b` for `a` in `b = c`.

You can think of `ring` like a more capable `norm_num`, which is capable of dealing with numbers and more able of manipulating expressions with variables. Moreover, `ring` is for closing goals and cannot be applied to hypothesis which is an advantage `norm_num` has. For this way of proving things, each line is a goal so using `ring` is appropriate.

If you want details, a 'ring' is an algebraic structure with an addition and multiplication operation satisfying some common sense properties. Alot of things like ... are rings. For more details, ...

The syntax of `calc` is as follows:
```
calc 
```

# `sorry`?
You are sorry you don't know the proof and Lean accepts that and closes the goal. Note: this is very dangerous because you might have Lean admit something that is false, which is not a good idea. Also, allowing `sorry` in this game would not let you solve every level by just typing `sorry`.

Replace every occurrence of `sorry` with a legitimate proof.
"

Statement (h : x = 3) (g: y = 6) (i : z=10) : x + x = y := by
{
  Template
    calc 
      x+x = 3+3 := by sorry
        _ = 6 := by sorry
        _ = y := by sorry
}
/-
  x+x = 3+3 := by rw [h]
    _ = 6 := by norm_num
    _ = y := by rw [←g]
-/



Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

NewTactic «calc»  
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

