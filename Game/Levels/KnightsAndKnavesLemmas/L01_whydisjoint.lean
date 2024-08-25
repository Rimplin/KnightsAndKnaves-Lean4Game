import Game.Metadata
--import Game.Levels.KnightsAndKnavesLemmas.L02_NotKnave_Knight

--#check notKnave_Knight
World "KnightsAndKnavesLemmas" 
Level 1

Title "" 

Introduction 
"
We can think of the set of knights and the set of knaves, denoted `Knights`, `Knaves` respectively. A set is a collection of 'entities' with a specified property. The set `Knight` would be the set of inhabitants of the island that are knights i.e satisfying the property of always telling the truth, the set `Knave` being the set of inhabitatns of the island that are knives i.e the ones that always lie. 

Note that in Lean, `Set K` means the set of objects of type `K`( this can be changed to something clearer?? think of clarity benefits of a change). Note that in each level, we will be considering two or three inhabitants of the island and will not be reasoning about the sets themselves but about these fixed inhabitants named `A`, `B`, `C`.

---------------------------------
Here we introduce Xor'. 
Many definitions capture the meaning we want: there is iff definition, and ∧ ∨ definition. 

We don't need these and can opt for a simpler assumption, 
"

#check xor_iff_not_iff
#check Xor'
/- (a ∧ ¬ b) ∨ (b ∧ ¬ a) -/
#check not_iff
/-
A ∈ Knight ∧ A ∉ Knave ∨ A ∈ Knave ∧ A ∉ Knight.
-/



/-
journey of formalization:
we first need to show that the assumption `h` is necessary then do this 'example'. show this using a concrete problem

the two sets Knight and Knave must be disjoint. You can't telll the truth and lie at the same time because if that is true, then you would be asserting `p ∧ ¬p` which can be used to derive `False` i.e a contradiction( you have shown in a previous level that `p ∧ ¬p → False`. This is not something we want, the puzzles would be meaningless. Of course, them being disjoint is not something to prove but a restriction we impose (so the puzzles make sense) because of the problem discussed in the previous paragraph.
-/ 
-- simplifying the conditions, also the Xor' conditions won't be necessary after the notKnave_Knight (etc ...) stuff

-- steps for showcasing formalization
/-
declaring the sets, the objects in question like A,B,C

implication for their statements with the negated version then why the two sets are disjoint
-/
Statement (Knight : Set K ) (Knave : Set K)
    -- x says y is a knight
  -- y says that x and y are of different type. this doesn't work here because we are emphasizing why they are disjoint, we have not established that they are disjoint yet... after asserting they are disjoint, now its possible to say statements like they are of different type
  --rules of the game, i.e knights tell the truth but knaves lie
  (stx : x ∈ Knight → y ∈ Knight) 
  (stxn : x ∈ Knave →  ¬ (y ∈ Knight)) 
  (h' : x ∈ Knight ∧ x ∈ Knave)
  : y ∈ Knight ∧ ¬(y ∈ Knight) := by 
  constructor 
  exact stx h'.left 
  exact stxn h'.right 

#check Set.inter_eq_right



-- knight_knave (h : x ∈ Knight) (h' : x ∈ Knave) : False , maybe extend contradiction to detect this...

Conclusion 
"
Note that the forward direction is always true, and our assumption `h` wasn't used, but the backward direction is not always( We used `h` for that). This offers a simplification and decluttering of the proof state and will be followed from now on. The downside is an apparent loss of information, but the coming levels will show that this is not the case.

(follow up to show that there was no loss of information)
"

/- Use these commands to add items to the game's inventory. -/

--NewTactic 
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
