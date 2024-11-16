import Game.Metadata

World "LogicTruthValue_" 
Level 1

Title "" 

Introduction 
"
<img src=\"https://pixabay.com/vectors/cat-kitty-child-animal-cute-baby-8943928\"/>

-- the user already knows what propositions are...............................
'The Lean theorem prover had a 4.70 release' is a true statement. After denoting this statement with `P`, we can say that `P` is `True` or `P = True`.

'World War 2 ended in 1950' is a false statement. It ended in 1945. After denoting this statement with `Q`, we can say that `Q` is `False` or `Q = False`.

# examples of propositions
You have seen propositions in 'Equational Reasoning'. Things like `x = 2`, `y = 6` are propositions i.e of type `Prop`. 

These are called atomic propositions. Atomic propositions are ones which contain no logical connectives (like the previously discussed `∧`). You will also learn how to make compound propositions from atomic propositions using logical connectives.

# experiment using editor mode
Editor mode is a vscode like environment. The main thing we want to emphasize this level is that you can hover over things to get more information.
Use `#check` and hover your mouse to see what it says.
Try:
```
#check 2=2
#check x=2
#check P=True 
...
```
In Lean, proving `P` or `P = True` is the same thing.
In other words, for `h : P` , `eq_true h : P = True`. Conversly, for `h : P = True` , `of_eq_true h : P = True`. This world will alternate between both perspectives. The first is primarily focused on valid manipulation of expression and the second is a more 'calculus' approach focused on substituting truth values and calculating...(need better explanation)
`#check` gives the type of the expression that's after it.
Notice that `P=True` is of type Prop which means that it is an assertion that is either `True` or `False`. It is true i.e `(P=True)=True` when we find a proof `h : (P = True)`. When faced with any expression of the form: someProp = True, this means that someProp is true. So here, `P=True` is a true statement which implies that `P` can be replaced by `True` wherever it occurs.
`((P = True) = True) = True` 
Note that a proof of `x = 2` was an `h : x = 2` and not `h : (x = 2) = True`. Here however, a proof of an arbitrary proposition `P` is `h : P = True` and not `h : P`. The latter would work as well, and you can go between the two using an appropriate theorem. The first perspective is emphasized in this world, and the second is emphasized in the world that follows.
The truth table perspective will make this less confusing.
Whenever you are done, replace `sorry` with `rfl` to close the goal and move on.

-------------------------

A proposition is a statement/assertion that can take only one of two values, either true or false. 
"
variable {P : Prop}
variable {h : P}
#check eq_true (of_eq_true (eq_true h))
#check eq_true
#check of_eq_true
/-- works here too? -/
Statement 
  : 2=2 := by
-- https://www.spyne.ai/image-enhancer

--```
--<img src=\"https://pixabay.com/vectors/cat-kitty-child-animal-cute-baby-8943928\"/>
--```
  {
  Hint "
<img src=\"https://www.spyne.ai/image-enhancer\"/>
  "
  Template
    Hole
  rfl
  }

Conclusion "<img src=\"https://pixabay.com/vectors/cat-kitty-child-animal-cute-baby-8943928/\">


<img src=\"data/g/JadAbouHawili/testing-leangame/Truth-Table-And.png\"/>
"

example (p q r : Prop) (hp : p) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption);

example (hq : q) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption);

example (p q r : Prop) (hr : r) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption);

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor <;> (try constructor) <;> assumption
