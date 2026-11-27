import Game.Levels.Power.L03_PowOne

World "Power"
Level 4

Title "`one_pow`"

VisualLevelNumber "10"

-- Experimental (V13.2): the screen after the level.
VisualPostLevel "Equality Unlocked!"
VisualPostLevelUnlock one_pow "No matter how many ones you multiply together, you’ll only ever get more ones."

namespace MyNat

/-- `one_pow n` is a proof that $1^n=1$. -/
TheoremDoc MyNat.one_pow as "one_pow" in "^"

Statement one_pow : ∀ m : ℕ, (1 : ℕ) ^ m = 1 := by
  exact fun m => by
    induction m with t ht
    · rw [pow_zero]
    · rw [pow_succ, ht, mul_one]
