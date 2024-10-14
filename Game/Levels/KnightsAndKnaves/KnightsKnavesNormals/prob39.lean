import Game.Metadata
import Mathlib.Data.Finset.Basic
#check Finset.mem_def
#check Set.toFinset

#check Finset.instCoeSortFinsetType
-- should be available, #check Finset.instCoeSortType

example 
  [inst : DecidableEq K]
  (A B C : K)
  (AneB : A ≠ B)
  (BneC : B ≠ C)
  (AneC : A ≠ C)
  (Knight : Finset K ) 
  (Knave : Finset K)
  {Normal : Finset K}
{OneKnight :  Knight.card =1 }
{OneKnave : Knave.card =1 }
{OneNormal : Normal.card =1 }

{hKKn : Knight ∩ Knave = ∅ }
{hKN : Knight ∩ Normal = ∅ }
{hKnN : Knave ∩ Normal = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave ∨ A ∈ Normal }
{h2 : B ∈ Knight ∨ B ∈ Knave ∨ B ∈ Normal }
{h3 : C ∈ Knight ∨ C ∈ Knave ∨ C ∈ Normal}
{stA : A ∈ Knight → (A ∈ Normal) } 
{stAn : A ∈ Knave → ¬ (A ∈ Normal) }
{stB : B ∈ Knight → (A ∈ Normal)}
{stBn : B ∈ Knave → ¬(A ∈ Normal)}
{stC : C ∈ Knight → C ∉ Normal}
{stCn : C ∈ Knave → C ∈ Normal}
: A ∈ Knave ∧ B ∈ Normal ∧ C ∈ Knight := by 
  /-
  AnKnight, If A were a knight then A would be a normal as well which is a contradiction
  -/ 
  have AnKnight : A ∉ Knight := by 
  {

    by_contra AKnight
    have ANormal := stA AKnight
    -- have to fix this
    --rw [KnightSet] at ANormal


-- disjoint here was Set version but now itsFinset version
    exact disjoint hKN AKnight ANormal
    --exact disjointfinset hKN AKnight ANormal
  }

  -- because AnKnight, then A either knave or normal
  -- AnNormal, if A were normal then BnKnave(maybe make a told the truth thing that would return A knight or normal)
  have AnNormal : A ∉ Normal := by
  {
    by_contra ANormal
    have BnKnave := (Function.mt stBn) (by push_neg; assumption)
    simp [BnKnave] at h2
    have BKnightNormal := h2

    -- helper theorem called full
    have BnNormal : B ∉ Normal := by
    {
      #check One
      exact full ANormal OneNormal AneB
      
      --by_contra BNormal
      --have AeqB:= by exact card_eq OneNormal  ANormal BNormal
      --contradiction
    }

    have BKnight := notleft_right (Or.symm BKnightNormal) BnNormal

    -- since A Normal, B Knight, then C Knave
    have CKnave : C ∈ Knave := by {
      rcases h3 with CKnight|CKnaveNormal
      ·   
        have BeqC := card_eq OneKnight BKnight CKnight
        contradiction
      · rcases CKnaveNormal with CKnave|CNormal
        · assumption
        · have AeqC := card_eq OneNormal ANormal CNormal
          contradiction 
    }

    have CNormal := stCn CKnave
    have AeqC := card_eq OneNormal ANormal CNormal
    contradiction
  }
  have AKnave : A ∈ Knave := by
  {
    simp [AnKnight,AnNormal] at h1
    assumption

  }
  have BnKnight :=  Function.mt stB AnNormal

  have BnKnave := full AKnave OneKnave AneB

  --have := notleft_right h2 BnKnight 
  --have BNormal := notleft_right this BnKnave   
 -- have BNormal := NotKnightKnave_Normal h2 BnKnight BnKnave
   

  -- now C is a knight by a similar reasoning... it is the only option left...
  -- A Knave , B Normal
  have CnKnave := full AKnave OneKnave  AneC
  --have CnNormal := full  BNormal  OneNormal BneC
 -- have := NotKnave_KnightNormal hKKn hKN hKnN  h3 CnKnave


 -- need to re-solve
  sorry
  --have CKnight := NotKnaveNormal_Knight h3 CnKnave CnNormal
  --constructor
  --· assumption
  --· constructor
  --  · assumption
  --  · assumption


#check Membership
#check Finset.instMembershipFinset
#check Set.mem_toFinset


-------------------------------
inductive Person | knight : Person | knave : Person | normal --| dontknow : Person 
open Person 
--def A : Person := Person.knight
--def B := Person
--def C := Person
--#check A
/-
disadvantages of using inductive types,  

-/
def isKnight : Person → Prop | knight => true | knave => false | normal => false 
def isKnave : Person → Prop | knight => false | knave => true | normal => false 
def isNormal : Person → Prop | knight  => false | knave  => false | normal  => true 

    
-- evalutes to whether stA true or not
-- any person here not just A
def statementA : Person → Prop | p  => match p with | knight => isNormal knight | knave =>(isNormal knave) | normal => true 
--def statementAmod := (isKnight A) →  (isNormal A)
def statmentB: Person  → Prop | p => match p with | knight => statementA knight | knave => ¬ (statementA knave)|normal => false -- here we don't know, B being normal we don't know if A's st is true or false|--normal => statementA normal
def statmentC: Person  → Prop | p => match p with | knight => ¬ (isNormal knight ) | knave => ¬ (isNormal knave) | normal => true

-- not clear from statementA what the actual statement of A is...
example  (A B C : Person) (hA : A = Knight) (hB : B = Knight)  : 2=2 := by 
  #check statementA 
  --#print statementA

  have stAatA:= statementA 
  -- can't see the statement
  -- not self contained, not easy to reuse
  -- would have to make a whole list of definitions to the user which would be very annoying, the user wont memorize what everything means and will refer to that list constantly, normally the user would just look at the proof state and know
  unfold statementA at stAatA
  have stAatB:= statementA B
   
  rfl 
example (A : Person ) ( h : A = normal): isNormal A := 
  by 
  rw [h]
  unfold isNormal
  rfl

--def solvev : Person  →  Person → Person  → Prop | A |  B|  C => (isKnight A ∧ statementA A) ∧ (isKnight B ∧ statmentB B) ∧ (isKnight C ∧ statmentC C)
--def solvevmod (A B C : Person):  Prop := (isKnight A ∧ statementA A) ∧ (isKnight B ∧ statmentB B) ∧ (isKnight C ∧ statmentC C)
--def tester : List (Person  × Person ×  Person):=[(knight, knave, normal),(knight, normal, knave),(knave, normal, knight),(normal,knight,knave),(normal,knave,knight),(knight,knight,knight),(knave,knave,knave),(normal,normal,normal)]
--
--#check List.permutations [normal,knave,knight]
---- not really showing the solution or reasoning, relying on lean to do it...
---- try all cases and subtitute
--def solution:= findSol(Person ×  Person ×  Person):=testpermutation.find(λ p, solve p.fst p.snd p.snd)
