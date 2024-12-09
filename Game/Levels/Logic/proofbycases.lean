Or.elim {a b c : Prop} (h : a ∨ b) (left : a → c) (right : b → c) : c
This is the basis for proof by cases. 
Since we know the disjunction for any prop p, `p ∨ ¬p` (standing in for `p ∨ ¬p` this is a good starting point. Doing cases em would essentially assume p (which is a) , then you would need to show the goal (which is c) proving the implication a → c, then assume ¬p (in this case b) then you would to show the goal (in this case c)  proving the implication b → c. After that is done, we can conclude that the goal (in this case `c`) is true
