import Game.Metadata
import Mathlib.Data.Finset.Basic
#check Finset.mem_def


/-
to solve issues, check membership and coercion here:

mathlib4 docs at DuckDuckGo
https://start.duckduckgo.com/lite/?q=mathlib4+docs

Search
https://leanprover-community.github.io/mathlib4_docs/search.html?sitesearch=https%3A%2F%2Fleanprover-community.github.io%2Fmathlib4_docs&q=Finset

Mathlib.Data.Finset.Basic
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Basic.html#Finset

Mathlib.Data.Finset.Basic
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Basic.html#Finset.instMembership

mathlib4/Mathlib/Data/Finset/Basic.lean at c3c78bbdb01c312bd5143e44a38e6cbc8deb4b90 · leanprover-community/mathlib4 · GitHub
https://github.com/leanprover-community/mathlib4/blob/c3c78bbdb01c312bd5143e44a38e6cbc8deb4b90/Mathlib/Data/Finset/Basic.lean#L166-L167

-/

-- two approaches:
-- directly as a finset
-- as a set with a fintype instance to enable conversion to finset
#check Set.toFinset

#check Finset.toSet 

    #check Finset.coe_inj
    #check Finset.coe_inter
    #check Finset.coe_empty
#check Set.mem_toFinset

      #check Finset.instCoeTCFinsetSet
      #check Finset.mem_coe
      #check Finset.coe_inj

      #check Finset.mem_coe.mpr 
      #check Finset.mem_coe.symm 
      #check Finset.mem_def.mp 
    #check or_left_comm
        #check Set.mem_toFinset
        #check Set.toFinset
example 
  --sets

  [inst : DecidableEq K]
  (A B C : K)
  (AneB : A ≠ B)
  (BneC : B ≠ C)
  (AneC : A ≠ C)
  (Knight : Finset K ) (Knave : Finset K)
  {Normal : Finset K}
--{hK : Finset Knight}
--{hKn : Finset Knave}
--{hN : Finset Normal}
--{finKnight : Fintype Knight}
--{finKnave : Fintype Knave}
--{finNormal : Fintype Normal}
{OneKnight : Finset.card ( Knight) =1 }
{OneKnave : Finset.card Knave =1 }
{OneNormal : Finset.card Normal =1 }

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
    --sorry
    -- have to fix this
    --rw [KnightSet] at ANormal

    -- when knight and normal are finsets,  disjoint doesn't work because it expects sets... making disjoint work or just use disjointfinset
    -- or make the original formalization in finsets...
    --exact disjoint hKN AKnight ANormal
    rw [Finset.coe_inj.symm] at hKN
    rw [Finset.coe_inter] at hKN
    rw[ Finset.coe_empty] at hKN
--      exact @disjoint K A (Finset.toSet Knight) (Finset.toSet Normal) hKN AKnight ANormal
    sorry
    --exact disjointfinset hKN AKnight ANormal
  }

  -- interesting observation:
  -- for the knight and knave only, all theorems are sets
  -- for the knight knave normal , i need finsets . why not make theorems for knight and knave also finset, model both situations as a finset.
  --rw [NotKnight_KnaveIff] at AnKnight 
  
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
      #check full
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
  #check NotKnightNormal_Knave
  have AKnave : A ∈ Knave := by
  {
    simp [AnKnight,AnNormal] at h1
    assumption

  }
  #check Function.mt
  have BnKnight :=  Function.mt stB AnNormal
  #check full
  /-

1. theorem full.{u_1} : ∀ {K : Type u_1} {A : K} {S : Finset K} (B : K), A ≠ B → S.card = 1 → A ∈ S → B ∉ S :=
   fun {K} {A} {S} B AneB One AinS BinS => AneB (card_eq One AinS BinS)
  -/
  have BnKnave := full AKnave OneKnave AneB

  --have := notleft_right h2 BnKnight 
  --have BNormal := notleft_right this BnKnave   
  have BNormal := NotKnightKnave_Normal h2 BnKnight BnKnave
   

  -- now C is a knight by a similar reasoning... it is the only option left...
  -- A Knave , B Normal
  have CnKnave := full AKnave OneKnave  AneC
  have CnNormal := full  BNormal  OneNormal BneC
  #check NotKnaveNormal_Knight
  #check NotKnave_KnightNormal
 -- have := NotKnave_KnightNormal hKKn hKN hKnN  h3 CnKnave

  have CKnight := NotKnaveNormal_Knight h3 CnKnave CnNormal
  constructor
  · assumption
  · constructor
    · assumption
    · assumption

-- this2: B ∈ Set.toFinset (Knight) := by
theorem memToFinset (Knight : Set K ) {finKnight : Fintype Knight} {hK : Finset Knight} (AKnight : A ∈ Knight) : A ∈ (Set.toFinset Knight) := by  
  exact Set.mem_toFinset.mpr AKnight

-- having a knight finset gives problems with membership, so keep it as set and then do Set.toFinset which requires a Fintype instance...(another way without going through Fintype instance??)
#check Membership
#check Finset.instMembershipFinset
theorem memToFinset2 {Knight : Set K } 
(finKnight : Fintype Knight) 
--{hK : Finset Knight} 
(AKnight : A ∈ Knight) 
--[@Finset.instMembershipFinset K] 
: A ∈ (Set.toFinset Knight) := by  
  exact Set.mem_toFinset.mpr AKnight

-- two options
#check Finset.toSet -- natural way
#check Set.toFinset -- needs fintype instance
#check Fintype

example  {Knight : Set K } 
{finKnight : Fintype Knight} 
--{hK : Finset Knight} 
(AKnight : A ∈ Knight) 
--[@Finset.instMembershipFinset K] 
: 2=2 := by 
  have := memToFinset2 finKnight AKnight
  rfl


variable (K : Type)
#check @Set.univ K
#check Set.mem_univ
example (A B C: K) ( all : ∀(x : K), x = A ∨ x = B ∨ x = C) : @Set.univ K = {A,B,C} := by
  
 -- unfold Set.univ

  exact (Set.eq_univ_of_univ_subset fun ⦃a⦄ a_1 => all a).symm

  --apply Set.ext 
  --intro x
  --constructor
  --sorry
  --sorry

  --· intro xUniv
  --  by_contra
  --· exact fun a => trivial

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
