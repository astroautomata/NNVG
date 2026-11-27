import Game.Levels.LessOrEqual.L02_LeRefl

World "LessOrEqual"
Level 3

Title "Non-negativity of ℕ"

VisualLevelNumber "2"

-- Experimental (V13.2): the screen after the level.
VisualPostLevel "Proposition Unlocked!"
VisualPostLevelUnlock zero_leq "Zero is a lower bound for the natural numbers."

namespace MyNat

Introduction
"
To solve this level, you need to build a number `c` such that `n = 0 + c`.
"

NewTheorem MyNat.eq_implies_leq

/-- `zero_leq n` is a proof that `0 ≤ n`. -/
TheoremDoc MyNat.zero_leq as "zero_leq" in "≤"

Statement zero_leq : ∀ n : ℕ, 0 ≤ n := by
  exact fun n => (⟨n, by rw [zero_add]⟩ : ∃ c, n = 0 + c)
