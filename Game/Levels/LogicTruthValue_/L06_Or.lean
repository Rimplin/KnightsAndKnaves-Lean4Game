import Game.Metadata

--```
--Or.intro_left (b : Prop) (h : a) : a ∨ b
--```
--- `Or.intro_right`

example (hP : P=True)
  : (P ∨ Q) = True := by

  {
  /-

```lean
Or.intro_left {a : Prop} (b : Prop) (h : a) : a ∨ b
```
***
Alias for `Or.inl`. 
***
*import Init.Prelude*
  -/
--    exact Or.intro_left Q hP

    -- include two ways to solve...
    rw [hP,true_or]
    --exact Or.intro_left Q hP
    /-
```lean
Or.inl {a b : Prop} (h : a) : a ∨ b
```
***
`Or.inl` is "left injection" into an `Or`. If `h : a` then `Or.inl h : a ∨ b`. 
***
*import Init.Prelude*
    -/
  }

Conclusion 
"
Notice that in the type of `Or.intro_left`, you need to explicitly give the type that will be used to the right of the `∨` but you don't need to do this for the type to the left of `∨`. How does Lean what to do? Well, the type of `Or.intro_left` is in fact:
```
Or.intro_left {a : Prop} (b : Prop) (h : a) : a ∨ b
```
The only difference is the curly braces. This means that `a` is an implicit argument. In other words, you don't need to give it explicitly, Lean will deduce it from the type of `h`. For example, if `h:P` where `P:Prop` then Lean will know that `a` is `P` and will put `P` to the left of `∨`.

You can avoid entering both `a` or `b` explicitly and instead use: 
```
Or.inl {a b : Prop} (h : a) : a ∨ b
```
Here, Lean will infer what the propositions are automatically.
"
