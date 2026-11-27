import Game.Levels.LessOrEqualBoss
import Game.Levels.Multiplication

World "AdvMultiplication"
Level 1

Title "`mul_leq_mul_right`"

VisualLevelNumber "0"

VisualTacticUses induction 1

-- Experimental (V13.2): the screen after the level.
VisualPostLevel "Proposition Unlocked!"
VisualPostLevelUnlock mul_leq_mul_right "Multiplying by the same natural number on two sides of an inequality preserves it (assuming the inequality is not strict, since we could multiply by zero!)"

namespace MyNat

Introduction
"
Let's warm up with an easy one, which works even if `t = 0`.
"

/-- `mul_leq_mul_right a b h t` is a proof that `a * t ≤ b * t`, where `h` is a proof of `a ≤ b`. -/
TheoremDoc MyNat.mul_leq_mul_right as "mul_leq_mul_right" in "*"

Statement mul_leq_mul_right (a b : ℕ) (h : a ≤ b) : ∀ t : ℕ, a * t ≤ b * t := by
  exact fun t => (h : ∃ c, b = a + c).elim (fun d hd =>
    (⟨d * t, by rw [hd, add_mul]⟩ : ∃ c, b * t = a * t + c))
