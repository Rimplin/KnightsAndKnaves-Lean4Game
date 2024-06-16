--import Game.Metadata


theorem contrapositive (forward: P → Q) :  ¬Q → ¬P := by

  {

    intro nq
    intro p
    exact nq (forward p)
}
