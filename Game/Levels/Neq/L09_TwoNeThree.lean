import Game.Levels.Neq.L08_OneNeZero

World "Neq"
Level 9

Title "2 ≠ 3"

VisualLevelNumber "8"

namespace MyNat

-- Unlocked by completing `one_ne_zero` (the level before).
/-- `zero_ne_one` is a proof of `0 ≠ 1`. -/
TheoremDoc MyNat.zero_ne_one as "zero_ne_one" in "012"

NewTheorem MyNat.zero_ne_one

Statement : (2 : ℕ) ≠ 3 := by
  exact fun h => zero_ne_succ 0 (succ_inj 0 1 (succ_inj 1 2 h))
