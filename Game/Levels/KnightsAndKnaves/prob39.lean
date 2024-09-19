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

New Tab
about:newtab
-/

-- two approaches:
-- directly as a finset
-- as a set with a fintype instance to enable conversion to finset
#check Set.toFinset


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
{hK : Finset Knight}
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
    --have KnightSet:=Finset.toSet Knight
    #check Set.toFinset
    --rw [KnightSet] at ANormal

    -- when knight and normal are finsets,  disjoint doesn't work because it expects sets... making disjoint work or just use disjointfinset
    #check Finset.coe_inj
    #check Finset.coe_inter
    #check Finset.coe_empty
    rw [Finset.coe_inj.symm] at hKN
    rw [Finset.coe_inter] at hKN
    rw[ Finset.coe_empty] at hKN
    exact @disjoint K A (Finset.toSet Knight) (Finset.toSet Normal) hKN AKnight ANormal
    --exact disjointfinset hKN AKnight ANormal
  }

  -- interesting observation:
  -- for the knight and knave only, all theorems are sets
  -- for the knight knave normal , i need finsets . why not make theorems for knight and knave also finset, model both situations as a finset.
  --rw [NotKnight_KnaveIff] at AnKnight 
  
  -- because AnKnight, then A either knave or normal
  have AKnaveNormal := disjunctiveSyllogism h1 AnKnight 
  -- AnNormal, if A were normal then BnKnave(maybe make a told the truth thing that would return A knight or normal)
  have AnNormal : A ∉ Normal := by
  {
    by_contra ANormal
    have BnKnave := (Function.mt stBn) (by push_neg; assumption)
    have BKnightNormal := NotKnave_KnightNormal hKKn hKN hKnN h2 BnKnave


    -- helper theorem called full
    have BnNormal : B ∉ Normal := by
    {
      #check full
      #check One
      exact full B AneB OneNormal ANormal
      
      --by_contra BNormal
      --have AeqB:= by exact card_eq OneNormal  ANormal BNormal
      --contradiction
    }

    have BKnight := disjunctiveSyllogism (Or.symm BKnightNormal) BnNormal

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
    exact NotKnightNormal_Knave hKN h1 AnKnight AnNormal
    --cases AKnaveNormal
    --assumption
    --contradiction

  }
  have BnKnight : B ∉ Knight := by
    { 
    intro h
    have := stB h
    contradiction
  }


  have BnKnave : B ∉ Knave := by{ 
    intro h_1
    have := card_eq OneKnave AKnave h_1
    contradiction
  }

  --have := disjunctiveSyllogism h2 BnKnight 
  --have BNormal := disjunctiveSyllogism this BnKnave   
  have BNormal := NotKnightKnave_Normal h2 BnKnight BnKnave
   

  -- now C is a knight by a similar reasoning... it is the only option left...
  have  CnKnave : C ∉ Knave := by 
    by_contra CKnave
    have AeqC := card_eq OneKnave AKnave CKnave
    contradiction
  have  CnNormal : C ∉ Normal := by 
    by_contra CNormal
    have AeqC := card_eq OneNormal BNormal CNormal
    contradiction
  #check NotKnave_KnightNormal
  have := NotKnave_KnightNormal hKKn hKN hKnN  h3 CnKnave
  cases h3
  · constructor
    assumption
    constructor
    assumption
    assumption
  · cases h
    contradiction
    contradiction

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
example (A B C: K) : @Set.univ K = {A,B,C} := by
  apply Set.ext 
  intro x
  constructor
  sorry
  sorry
  --· intro xUniv
  --  by_contra
  --· exact fun a => trivial

--inductive Person | knight : Person | knave : Person | normal : Person
--open Person def isKnight : Person → Prop | knight => true | knave => false | normal => false 
--def isKnave : Person → Prop | knight => false | knave => true | normal => false 
--def isNormal : Person → Prop | knight  => false | knave  => false | normal  => true 
--def statementA : Person → Prop | p  => match p with | knight => isNormal knight | knave =>(isNormal knave) | normal => true 
--def statmentB: Person  → Prop | p => match p with | knight => statementA knight | knave => ¬ (statementA knave)|normal => statementA normal
--def statmentC: Person  → Prop | p => match p with | knight => ¬ (isNormal knight ) | knave => ¬ (isNormal knave) | normal => true
--def solve : Person  →  Person → Person  → Prop | A B C => (isknight A ∧ statementA A) ∧ (isknight B ∧ statementB B) ∧ (isknight C ∧ statementC C)
--def tester : List (Person  × Person ×  Person):=[(knight, knave, normal),(knight, normal, knave),(knave, normal, knight),(normal,knight,knave),(normal,knave,knight),(knight,knight,knight),(knave,knave,knave),(normal,normal,normal)]
--
--def solution:= findSol(Person ×  Person ×  Person):=testpermutation.find(λ p, solve p.fst p.snd p.snd)
