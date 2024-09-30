import GameServer.Commands
import Game.LevelLemmas.Logical
import Game.LevelLemmas.KnightsAndKnaves
--import Mathlib.Tactic
--import Mathlib.Util.Delaborators
--import Mathlib

import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Qify
import Mathlib.Tactic.Polyrith
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.ApplyFun
--import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Basic

/-! Use this file to add things that should be available in all levels.

For example, this demo imports the mathlib tactics

*Note*: As long as `Game.lean` exists and ends with the `MakeGame` command,
you are completely free how you structure your lean project, this is merely
a suggestion.

*Bug*: However, things are bugged out if the levels of different worlds are imported
in a random order. Therefore, you should keep the structure of one file lean file per world
that imports all its levels.
-/
