import Game.Levels.Neq.L08_OneNeZero

World "Neq"
Level 9

Title "2 ≠ 3"

VisualLevelNumber "8"

-- Experimental (V13.1): the screen the spec puts between level 7 and this one, as a
-- pre-level with this title, for the two theorems level 7 leaves the player with.
VisualPreLevel "Axiom Proposition Unlocked!"
VisualPreLevelUnlock one_ne_zero
VisualPreLevelUnlock zero_ne_one
VisualPreLevelText "You heard it here first, folks!

Zero does *not* equal one!"

namespace MyNat

-- Unlocked by completing `one_ne_zero` (the level before).
/-- `zero_ne_one` is a proof of `0 ≠ 1`. -/
TheoremDoc MyNat.zero_ne_one as "zero_ne_one" in "012"

NewTheorem MyNat.zero_ne_one

Statement : (2 : ℕ) ≠ 3 := by
  exact fun h => zero_ne_succ 0 (succ_inj 0 1 (succ_inj 1 2 h))
