import Game.Levels.LessOrEqual
import Game.Levels.InductionDouble

World "LessOrEqualJoined"
Level 1

Title "Nothing Smaller than Zero"

VisualLevelNumber "7"

-- Experimental (V13.2): the screen after the level.
VisualPostLevel "Proposition Unlocked!"
VisualPostLevelUnlock leq_zero "Zero is the greatest lower bound for the natural numbers."

namespace MyNat

Introduction
"
It's \"intuitively obvious\" that there are no numbers less than zero,
but to prove it you will need `add_right_eq_zero` from Induction World.
"

/-- `leq_zero n` is a proof of `n ≤ 0 → n = 0`. -/
TheoremDoc MyNat.leq_zero as "leq_zero" in "≤"

Statement leq_zero (n : ℕ) (hn : n ≤ 0) : n = 0 := by
  exact (hn : ∃ c, 0 = n + c).elim (fun c hc => add_right_eq_zero n c hc.symm)
