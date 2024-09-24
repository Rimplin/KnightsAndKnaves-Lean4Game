import Game.Metadata

#check 2=2

#check Set.inter_inter_inter_comm
#check Set.inter_left_comm
example
  --sets
  {Knight : Set Inhabitant} 
  {Knave : Set Inhabitant}
  {Normal : Set Inhabitant}
  (h'' : Xor' (A ∈ Knight) (  (A ∈ Knave ∪ Normal) ᶜ   ) )
{hKKn : Knight ∩ Knave = ∅ }
{hKN : Knight ∩ Normal = ∅ }
{hKnN : Knave ∩ Normal = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave ∨ A ∈ Normal }
{h2: B ∈ Knight ∨ B ∈ Knave ∨ B ∈ Normal}
{AKnight : A ∈ Knight}
{ANormal : A ∈ Normal}
--{stA : A ∈ Knight → () }
--{stAn : A ∈ Knave → ¬ () }
--{stB: B ∈ Knight → () }
--{stBn: B ∈ Knave → ¬ () }
  : False:= by

  {
    -- disjoint is very useful, need versions for Knight_NotKnaveNotNormal
    unfold Xor' at h''
    exact disjoint hKN AKnight ANormal     
 
    
  }



newkkn
