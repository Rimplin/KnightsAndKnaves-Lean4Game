import Game.Metadata

-- similar to second way??
variable (Knight : Inhabitant →  Prop)
variable (Knave : Inhabitant →  Prop)
--def Knight(x : Inhabitant) : Prop := sorry
example (A B : Inhabitant) : Knight A := by
  cases em (Knight A)
  · sorry
  · sorry
