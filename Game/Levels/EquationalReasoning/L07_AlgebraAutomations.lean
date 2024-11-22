import Game.Metadata

World "EquationalReasoning" 
Level 7

Title "Automations" 

Introduction 
"
This level introduces automations for the kinds of algebra problems you have previously encountered. Many can be solved using one tactic!!! This is useful for statements for statements that you have to prove but are considered to be 'trivial'.

In fact, you have already seen automations. `norm_num` for example.
"

--ring
--simp
--omega
--linarith

example (y : ℕ) (h:3*y=12) : y=4 := by
  apply Nat.mul_left_cancel three_pos
  rw [h]
  norm_num

example (y : ℕ) (h:3*y=12) : y=4 := by
  qify at h ⊢
  apply_fun (·/3) at h
 -- norm_num at h
  simp at h
  rw [h]
  norm_num

example (y : ℕ) (h:3*y=12) : y=4 := by
  apply_fun (3*·)
  simp
  exact h
  refine mul_right_injective₀ ?_
  norm_num
