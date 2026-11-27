import Game.Levels.LessOrEqualBonus.L01_Gt

World "LessOrEqualBonus"
Level 2

Title "Irreflexivity of `>`"

VisualLevelNumber "A1"

-- Experimental (V13.2): the screen after the level. (Its text is the spec's, word
-- for word.)
VisualPostLevel "Proposition Unlocked!"
VisualPostLevelUnlock lt_not_refl "A binary operation `·` is *irreflexive* if, for all `n` in the domain, `n · n` never holds."

namespace MyNat

Introduction
"
No number is greater than itself.
"

/-- `lt_not_refl n` is a proof of `¬ (n > n)`. -/
TheoremDoc MyNat.lt_not_refl as "lt_not_refl" in ">"

Statement lt_not_refl : ∀ n : ℕ, ¬ (n > n) := by
  exact fun n h => h (leq_refl n)
