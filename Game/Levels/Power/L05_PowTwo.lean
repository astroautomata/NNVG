import Game.Levels.Power.L04_OnePow

World "Power"
Level 5

Title "`pow_two`"

VisualLevelNumber "11"

-- No induction in this level.
VisualTacticUses induction 0

-- Experimental (V13.2): the screen after the level.
VisualPostLevel "Equality Unlocked!"
VisualPostLevelUnlock pow_two "Squaring is just multiplying something by itself."

namespace MyNat

Introduction
"
Note: this lemma will be useful for the final boss!
"

/-- `pow_two a` says that `a ^ 2 = a * a`. -/
TheoremDoc MyNat.pow_two as "pow_two" in "^"

Statement pow_two : ∀ a : ℕ, a ^ 2 = a * a := by
  exact fun a => by rw [two_eq_succ_one, pow_succ, pow_one]
