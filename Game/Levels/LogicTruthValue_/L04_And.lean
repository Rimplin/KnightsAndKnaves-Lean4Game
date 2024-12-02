import Game.Metadata

Introduction 
"
In this level, we will learn about the `∧` logical connective, known as 'And'.
In logic, for `P,Q` propositions, `P ∧ Q` is true when both `P` is true and `Q` is true, being false otherwise.

# Logical Connectives
It is important to note that connecting two proposition via a logic connective results in a proposition as well. This proposition, like any other proposition, has a truth value. This truth value depends on the truth value of the propositions it was built out of and the rules of the logical connective. This is clearly illustrated in a truth table. 

## example

Let `p` denote the proposition 'The official language of France is french'(which is true).
Let `q` denote the prposition 'The official language of Germany is german'(which is true as well).
Combining these two prpositions together gives us the proposition `p ∧ q` which translated to English: 'The official language of France is french `And` the official language of Germany is german'. Because the two propositions connected by the `And` are true, then the entire statement is true as well. It's not hard to see that one of or both `p` or `q` being false would make `p ∧ q` false. In other words, `p ∧ q` is true when `p` is true and `q` is true. It is false otherwise.
"

-- treat P, Q as variables. similar to x=2, not necessarily a unique perspective
example (hP : P=True) (hQ : Q=True) (hPQ: P ∧ Q)
  : (P ∧ Q) = True  := by

  {
    -- no theorem to directly get this, maybe do a calc proof??? compare that to other approaches of logical proof.
    #check True.intro
    #check True

    #check hP
    #check P=True
   -- rw [hP,hQ]
   -- apply and_true 

    calc 
        (P ∧ Q) = (True ∧ Q) := by rw [hP]
        _ = (True ∧ True) := by rw [hQ] 
        _ = True := by exact and_true True

 --   refine 
    --Hint (hidden:=true) "Try `exact And.intro hP hQ` or `constructor`" 
    --Branch
    --   exact And.intro hP hQ 
    --constructor
    --Hint "Notice that the goal is now `P`"
    --exact hP
    --Hint "After closing the goal `P`, you now have to close the goal `Q`"
    --exact hQ
  }

Conclusion 
"
The constructor tactic transformed the goal `P ∧ Q` into two subgoals the first being `P` and the second being `Q`. This way of doing things matches the meaning of the `∧` connective.
"
