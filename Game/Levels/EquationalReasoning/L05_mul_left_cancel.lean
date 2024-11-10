import Game.Metadata

import Game.Doc.doc

World "EquationalReasoning" 
Level 5 

Title "some title" 

Introduction 
"
Here we introduce the `have` tactic which allows us to add theorems to the context(which you would have to prove, of course). 

We will add the theorem `16=4*4` to the proof state, and use it to prove the goal.

Heres an example:
`have twoEqualstwo : 2=2 := by rfl` will add an object named `twoEqualstwo` of type `2=2` to the proof state which would look as follows:
```
Assumptions:
twoEqualstwo : 2=2
```

You can choose any name after `have` and any type after `:`.

For this problem, we want `16=4*4` instead of `2=2`.
Adapt this example to `16 = 4*4` and include after `by` its proof.


"

Statement (h : 4*y=16) : y = 4 := by{
  Hint (hidden := true) 
  "
  For the proof, we need to carry out the calculation of `4 * 4` and as in the previous level, the tactic for that is `norm_num`. Typing that as the proof will work. 
  "
  --Template
 -- have helper: 16=4*4 := by norm_num
 -- --Hole
 -- rw [helper] at h
 -- exact mul_left_cancel₀ four_ne_zero h
 
  --Hint (hidden := true) (strict := true) "Try `have helper : 16=4*4 := by norm_num`" 
  -- Notice that if `16` were in the goal, you would do `rw [{helper}]` to replace `16` with with `4*4`. We want to do the same thing at `h`. So, `rw ... at h` will do it. 
  have helper : 16=4*4 := by norm_num 
  Hint "Now, using `rw`, we want to replace the `16` in `h` with `4 * 4`. "
  -- In other words, we want to do `rw [{helper}]` and have it be applied on h. 
  Hint (hidden := true) "`rw [{helper}] at h`" 
  rw [helper] at h 
  Hint "
 Using `mul_left_cancel₀`, cancel the `4` on both sides of `h` obtaining `y=4` which is the goal.

  For example, given the following proof state:
  ```
  equation : 2*x = 2*3
  ```
  `mul_left_cancel₀` is of the form:
  ```
  mul_left_cancel₀ firstArgument secondArgument
  ```

  The following expression cancels `3` from both sides of `equation`:
  ```
  (mul_left_cancel₀ two_ne_zero equation) : x =3 
  ```

  Note that:
  ```
  two_ne_zero : 2 ≠ 0
  ```
  where 'ne' stands for not equal.

  Arguments are given without paranthesis
  is the first argument given to `mul_left_cancel₀` and `equation` is the second.

  Adapt this to the current problem.
  "
  /-
   Arguments are given without parenthesis, for example :
   ```
   mul_left_cancel₀ ha h
   ```
   The theorem then cancels `a`(`4`) from both sides giving a proof of `b=c`(`y=4`). This is exactly what we want to prove the goal.
  -/
  Hint (hidden:=true) "
  Notice that `mul_left_cancel₀ four_ne_zero h` has type `y = 4`. So, `exact mul_left_cancel₀ four_ne_zero h` will do it."
  exact mul_left_cancel₀ four_ne_zero h
}

Conclusion 
"
Here is the type signature of mul_left_cancel\\0:
  ```
  mul_left_cancel\\0 (ha : a ≠ 0) (h : a * b = a * c) : b = c
  ```
  `mul_left_cancel₀` takes two arguments which are:
   - `ha`, a proof that some number `a` is not equal to zero. 
   - `h`, the equation which has `a` on both sides of the equation multiplied on the left.

  The result is canceling `a` from both sides of the equation.
"
--In our case `h` is the `h` in our assumptions and `a` is `4`, `four_ne_zero` is the argument you should give.
--you want to cancel from both sides of `h` is 
#check add_mul
NewTactic «have» 

#check Nat.mul_left_cancel
#check mul_left_cancel

/-- [[mathlib_doc]] -/
TheoremDoc mul_left_cancel₀ as "mul_left_cancel₀" in "*"
NewTheorem mul_left_cancel₀ four_ne_zero

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
