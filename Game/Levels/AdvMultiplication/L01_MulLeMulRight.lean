import Game.Levels.LessOrEqualBoss
import Game.Levels.Multiplication

World "AdvMultiplication"
Level 1

Title "`mul_le_mul_right`"

VisualLevelNumber "0"

namespace MyNat

Introduction
"
Let's warm up with an easy one, which works even if `t = 0`.
"

/-- `mul_le_mul_right a b h t` is a proof that `a * t ≤ b * t`, where `h` is a proof of `a ≤ b`. -/
TheoremDoc MyNat.mul_le_mul_right as "mul_le_mul_right" in "*"

Statement mul_le_mul_right (a b : ℕ) (h : a ≤ b) : ∀ t : ℕ, a * t ≤ b * t := by
  exact fun t => (h : ∃ c, b = a + c).elim (fun d hd =>
    (⟨d * t, by rw [hd, add_mul]⟩ : ∃ c, b * t = a * t + c))
