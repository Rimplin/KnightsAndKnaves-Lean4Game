import Game.Metadata

-- first formalize the normals set
-- establish they are all disjoint
-- then get the disjiont equivalent for htis

-- Knight
-- Knave
-- Normal
-- many cases of having an element in two sets, all of them should contradict h
example
  --sets
  {Knight : Set Inhabitant} 
  {Knave : Set Inhabitant}
  {Normal : Set Inhabitant}
  -- this means simultaneously knight,knave ,knave, but being a knave and a normal is also something we don't want.
{h : Knight ∩ Knave ∩ Normal = ∅ }
{h1 : Xor' (A ∈ Knight) (A ∈ Knave) }
{h2: Xor' (B ∈ Knight)  (B ∈ Knave) }
{stA : A ∈ Knight → () }
{stAn : A ∈ Knave → ¬ () }
{stB: B ∈ Knight → () }
{stBn: B ∈ Knave → ¬ () }
  :  := by

  {
    #check Set.inter_inter_inter_comm
 
    
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

