import Game.Metadata

World "KnightsAndKnaves" 
Level 3

Title "" 

Introduction 
"
A says I am a knave or B is a knave. Notice stAn, which represents the fact that A's statement is false when A is a knave ( and viceversa of course). So the statement 'A is a knave or B is a knave' is false. What does it mean for an or expression to be false. It means that both sides are false.


--------------------- put these in hints
If A is a knave, then the statement 'A is a knave or B is a knave' is false which means that A is not a knave and B is not knave. A is not a knave but we previously assumed that A is a knave. Assuming A is a knave gives us a contradiction which means that A is not a knave.

This is the first part of the proof.

Now that we know that A is not a knave, then A is a knight. So we can conclude A is a knave or B is a knave. Since A is not a knave, we are left with one option which is B being a knave.

This concludes the proof.
"

-- A says I am a knave or B is a knave
Statement 
{inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{all2 : ∀ (x : Inhabitant), x = A ∨ x = B}
{Or : ∀(x :Inhabitant), x ∈ Knight ∨ x ∈ Knave}
{stA : A ∈ Knight ↔ (A ∈ Knave ∨ B ∈ Knave) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∨ B ∈ Knave) }
: A ∈ Knight ∧ B ∈ Knave := by 
  -- explain this
  --push_neg at stAn 

  have AnKnave : A ∉ Knave := by 
    -- maybe have these astemplate
    intro AKnave
    have ABK := stAn.mp AKnave 
    -- teach this??
    -- prove A ∈ Knave ∨ B ∈ Knave
    exact ABK (by left ; assumption)

   -- exact ABK.left AKnave

  have AKnight := notinright_inleft (Or A)  AnKnave
  have AorBKn := stA.mp AKnight
  simp [AnKnave] at AorBKn
  constructor
  repeat assumption

Conclusion 
"
"
