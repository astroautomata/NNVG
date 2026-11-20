import Game.Levels.Neq.L08_OneNeZero

World "Neq"
Level 9

Title "2 ≠ 4"

VisualLevelNumber "8"

namespace MyNat

-- Unlocked by completing `one_ne_zero` (the level before).
/-- `zero_ne_one` is a proof of `0 ≠ 1`. -/
TheoremDoc MyNat.zero_ne_one as "zero_ne_one" in "012"

NewTheorem MyNat.zero_ne_one

Statement : (2 : ℕ) ≠ 4 := by
  exact fun h => zero_ne_succ 1 (succ_inj 0 2 (succ_inj 1 3 h))
