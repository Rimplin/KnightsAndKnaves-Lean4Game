import Game.Metadata

import Game.Doc.doc

World "EquationalReasoning" 
Level 5 

Title "some title" 

Introduction 
"
Here we introduce the `have` tactic which allows to add theorems to the context(which you would have to prove, of course). The `mul_left_cancel₀` will not be used in future levels, but is given here for the sake of having a familiar example.

Proving the goal will go as follows:

1- Prove that `16=4*4`

2- Replace the `16` in `h` by `4*4`

3- Cancel the `4` on both sides of `h` obtaining `y=4` which is the goal. (using the theorem `mul_left_cancel₀`)

Step 1: ***Proving `16=4*4`***.
We need to construct an object of type `16 = 4 * 4`. Lean does not have such an object in its math library so we will have to prove it ourselves and add it to the current proof state. 
This is exactly what `have` does, which obeys the following syntax:
```
`have name-of-object : type := by ...` 
```
where `...` is the proof.
`name-of-object` can be whatever you want, leaving it empty would  give the theorem a name automatically. The `type` in this case is the statement we want to prove , i.e `16=4*4`. For the proof, we need to carry out the calculation of `4 * 4` and as in the previous level, the tactic for that is `norm_num`. Typing that as the proof will work. 
"

/-
There is an alternative syntax for `have` which you can view in the right side pane. In any case, it will be introduced later on when its more convenient to use.
`have name := ........`
-/
Statement (h : 4*y=16) : y = 4 := by{
  --Template
 -- have helper: 16=4*4 := by norm_num
 -- --Hole
 -- rw [helper] at h
 -- exact mul_left_cancel₀ four_ne_zero h
 
  --Hint (hidden := true) (strict := true) "Try `have helper : 16=4*4 := by norm_num`" 
  have helper : 16=4*4 := by norm_num 
  Hint "Now we want to replace the `16` in `h` with `4 * 4`. "
  -- In other words, we want to do `rw [{helper}]` and have it be applied on h. 
  Hint (hidden := true) "`rw [{helper}] at h`" 
  rw [helper] at h 
  Hint "
  Now that we have `4` on both sides, we want to cancel this `4`

  This is possible using the theorem `mul_left_cancel₀` which has the following type :
  ```
  mul_left_cancel₀(ha : a ≠ 0) (h : a * b = a * c) : b = c
  ```
  `mul_left_cancel₀` takes two arguments which are:
   - a proof that what you want to cancel is not equal to zero (in this case `a`).
   - the equation you are working with.
   The theorem then cancels `a` from both sides giving a proof of `b=c`. This is exactly what we want to prove the goal.

  To write the subscript in `mul_left_cancel₀`, do backslash zero. \\0 `mul_left_cancel₀` is written as `mul_left_cancel\\0`
  Lean has the theorem `four_ne_zero : 4≠0` which you need.
  "
  Hint (hidden:=true) "
  Notice that `mul_left_cancel₀ four_ne_zero h` has type `y = 4`. So, `exact mul_left_cancel₀ four_ne_zero h` will do it."
  exact mul_left_cancel₀ four_ne_zero h
}

Conclusion ""

#check add_mul
NewTactic «have» 
/- Focus on the type of `four_pos : 0 < 4`. The rest is just arguments that if you don't pass to Lean, Lean will deduce automatically. You can always learn what they mean by refering to the mathlib documentation -/
--TheoremDoc four_pos as "four_pos" in ">0"

/-

  `Nat.mul_left_cancel` takes two arguments, the first `np` is a proof that what you are cancelling from both sides of the equation is positive, and the second `h` is the equation itself. Its type is the equation `h` with `n` cancelled from both sides.

  In our cases, we want a proof that `4` is positive which is `four_pos : 0 < 4` and the equation we are working with which is `h`
-/
/-- [[mathlib_doc]] -/
TheoremDoc mul_left_cancel₀ as "mul_left_cancel₀" in "*"
NewTheorem mul_left_cancel₀ four_ne_zero
-- NewDefinition Nat Add Eq

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
NewDefinition UnicodeSymbols
