import Game.Levels.LessOrEqual
import Game.Levels.InductionDouble

World "LessOrEqualJoined"
Level 1

Title "Nothing Smaller than Zero"

VisualLevelNumber "6"

namespace MyNat

Introduction
"
It's \"intuitively obvious\" that there are no numbers less than zero,
but to prove it you will need `add_right_eq_zero` from Induction World.
"

/-- `le_zero x` is a proof of `x ≤ 0 → x = 0`. -/
TheoremDoc MyNat.le_zero as "le_zero" in "≤"

Statement le_zero (x : ℕ) (hx : x ≤ 0) : x = 0 := by
  exact (hx : ∃ c, 0 = x + c).elim (fun c hc => add_right_eq_zero x c hc.symm)
