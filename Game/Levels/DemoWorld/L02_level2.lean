import Game.Metadata

World "DemoWorld"
Level 2

Title "Hello World"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

Statement (h : x = 3) (g: y = 6) (i : z=10) : x + x = y := by
  Hint "You can either start using `{h}` or `{g}`."
  Branch
    rw [g]
    Hint "You should use `{h}` now."
    rw [h]
  rw [h]
  Hint "You should use `{g}` now."
  rw [g]

Conclusion "This last message appears if the level is solved."

example (h : 2 * a ≤3 * b) (h' : 1 ≤a) (h'' : d = 2) : d + a ≤5 * b := by{
  --suggest_tactics
  --simp [h'', le_refl]

}
