import Game.Metadata

-- first formalize the normals set
-- establish they are all disjoint
-- then get the disjiont equivalent for htis

-- Knight
-- Knave
-- Normal
-- many cases of having an element in two sets, all of them should contradict h


#check Set.inter_inter_inter_comm
#check Set.inter_left_comm
example
  --sets
  {Knight : Set Inhabitant} 
  {Knave : Set Inhabitant}
  {Normal : Set Inhabitant}
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
    exact disjoint hKN AKnight ANormal     
 
    
  }



example   {Knight : Set Inhabitant} 
  {Knave : Set Inhabitant}
  {Normal : Set Inhabitant}
  {h : (Knight ∩ Knave) ∩ Normal = ∅}
  {AKnight : A ∈ Knight}
  {AKnave : A ∈ Knave}
  : False := by 
    have := Set.mem_inter AKnight AKnave
    -- doesn't work, find another way, list all the possible intersections as empty??? wouldn't this be messy??
    rw [h] at this
Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/



-- NewTactic rw rfl
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

