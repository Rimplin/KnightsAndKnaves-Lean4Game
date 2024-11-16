import Game.Metadata
import Game.LevelLemmas.Logical

set_option trace.Meta.Tactic.simp true

#print Xor'
#check Xor
#check not_xor

#check not_iff
#check Xor'
#check and_iff_not_or_not
#check iff_iff_and_or_not_and_not
#check not_iff_not

#check not_iff_not
#check xor_iff_not_iff
#check xor_iff_iff_not
#check xor_iff_not_iff'
#check iff_iff_and_or_not_and_not
#check or_self

#check HEq
#check Eq

example 
  {inst : DecidableEq K}
  (Knight : Finset K ) (Knave : Finset K)
  (h : Knight ∩ Knave = ∅ ) (h1 : x ∈ Knight ∨ x ∈ Knave) (h2 : y ∈ Knight ∨ y ∈ Knave) 

  -- x says y is a knight
  -- y says that x and y are of different type
  --rules of the game, i.e knights tell the truth but knaves lie
  (stx : x ∈ Knight ↔ y ∈ Knight)
  (sty : y ∈ Knight ↔ (y ∈ Knight ∧ x ∈ Knave) ∨ (y ∈ Knave ∧ x ∈ Knight ) )
  (styn : y ∈ Knave ↔ ¬( (y ∈ Knight ∧ x ∈ Knave) ∨ (y ∈ Knave ∧ x ∈ Knight )) )
  --(styn : y ∈ Knave ↔ x ∉ Knave ∨ y ∉ Knight)
  : x ∈ Knave ∧ y ∈ Knave := by
    rw [not_or] at styn
    rw [not_and_or] at styn
    rw [not_and_or] at styn
    -- assuming x knight, we get y knight, then we get x and y are different type which is contradiction. so x knave which means y not knight i.e y knave. 

    sorry

example 
  {inst : DecidableEq K}
  (Knight : Finset K ) (Knave : Finset K)
  (h : Knight ∩ Knave = ∅ ) (h1 : x ∈ Knight ∨ x ∈ Knave) (h2 : y ∈ Knight ∨ y ∈ Knave) 

  -- x says y is a knight
  -- y says that x and y are of different type
  --rules of the game, i.e knights tell the truth but knaves lie
  (stx : x ∈ Knight ↔ y ∈ Knight)
  (sty : y ∈ Knight ↔ x ∈ Knight ∧ y ∈ Knave ∨ x ∈ Knave ∧ y ∈ Knight)
  : x ∈ Knave ∧ y ∈ Knave := by
  #check IfToIff

  rw [not_iff_not.symm] at stx

  rw [notinleft_inrightIff h1 h] at stx
  rw [notinleft_inrightIff  h2 h] at stx
  rw [stx]
  simp 

  have this:=h2

  cases h2 
  rw [sty] at h_1 
  rw [stx] at h_1
  nth_rw 1 [stx.symm] at h_1
  rw [inright_notinleftIff h1 h]  at h_1
  rw [inright_notinleftIff this h]  at h_1
  rcases h_1 with ⟨a,b⟩|⟨a',b'⟩  
  contradiction
  contradiction

  assumption
