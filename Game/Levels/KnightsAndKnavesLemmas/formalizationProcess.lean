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

-- simplifying the conditions, also the Xor' conditions won't be necessary after the notKnave_Knave (etc ...) stuff

-- scrap this??
example (Knight : Set Inhabitants ) (Knave : Set Inhabitants) (A : Inhabitants)
(h : Knight ∩ Knave = ∅ ) : Xor' (A ∈ Knight) (A ∈ Knave) ↔ A ∈ Knight ∨ A ∈ Knave := by 
  constructor
  unfold Xor' at *
  · intro h'
    cases h'
    · exact Or.inl (h_1.left)
    · exact Or.inr (h_1.left)

  · intro h'
    unfold Xor'
    cases h'
    · left
      constructor
      assumption
      -- this is just KnightNotKnave, introduce those two first then this... nice!
      by_contra
      have := Set.mem_inter h_1 a
      rw [h] at this
      contradiction
    · right
      constructor
      assumption
      by_contra
      have := Set.mem_inter a h_1
      rw [h] at this
      contradiction

-- from implication to if and only if

example (h : p → q) (h' : ¬p → ¬q) : p ↔ q := by 
  constructor
  · assumption
  · intro hq
    exact (Function.mtr h') hq

Conclusion 
"
"

