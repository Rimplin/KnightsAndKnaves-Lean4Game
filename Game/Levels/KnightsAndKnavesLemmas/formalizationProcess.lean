import Game.Metadata

World "KnightsAndKnavesLemmas"
Level 2

Title ""

#check XorToOr
#check IffToIf

Introduction 
"

3. inductive type interpretation?  
variable (Inhabitant : Type)
#check (Sum Inhabitant Inhabitant
variable (A : Sum Knight Knave)
variable (B : Knight)
example : 2=2 := by sorry

---------------------
-- xor approach
2. We can capture this in logic by saying that for any inhabitant say `A`, (`A` is a knight and is not a knave) or (`A` is a knave and is not a knight).

---- transition from xor approach to or
XorToOr
Then, for any inhabitant of the island they are either a knight or a knave but not both. In other words, if they are a knight then they can't be a knave and if they are a knave they can't be a knight. This can be translated to : (x is a knight and x is not a knave) or (x is a knave and is not a knight). This can be simplified to just saying that: (x is a knight) or (x is a knave) conveying the same information. In the first case (x being a knight), we know the two sets are disjoint so x can't be a knave. Similarly for the second case. This simpler statement conveys the same information as the former which is more complicated, so it should ie be used instead.

---------------------

two approaches:
the xor' , implication
the or, logical equivalence
This is significant, them being disjoint will allow us to conclude that if x ∈ Knight then x ∉ Knave.
This is because if x ∈ Knight, and we assume then x ∈ Knave then this would contradict the fact that the two sets are disjoint. This is called a proof by contradiction.

-----------------------------
Demonstrate that this information is redundant.
x ∈ Knight → x ∉ Knave

How do we express the fact that every inhabitant is either a knight or a knave?
The direct translation would be:
```
x ∈ Knight ∨ x ∈ Knave:
```
----------------------------
Now that we have justified why Knight and Knave are disjoint, how do we express the fact that every inhabitant is either a knight but not a knave or a knave but not a knight? 
The direct translation of this would be: 
```
(x ∈ Knight ∧ x ∉ Knave) ∨ (x ∈ Knave ∧ x ∉ Knight)
```
However, if we know that x ∈ Knight then because the two sets are disjoint, x ∉ Knave because if it were then the sets wouldn't be disjoint. This is the reasoning of this level but in terse informal english. x cannot be a knave because if it were then it would contradict the assumption that the two sets are disjoint.
"

Conclusion 
"
"

