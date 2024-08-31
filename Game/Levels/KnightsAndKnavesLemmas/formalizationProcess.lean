import Game.Metadata


World "KnightsAndKnavesLemmas"
Level 2

Title ""

Introduction 
"
"



--World "KnightsAndKnavesLemmas"
--Level 

Title ""

Introduction 
"
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

