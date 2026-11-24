import Game.Levels.Power.L06_PowAdd

World "Power"
Level 7

Title "`mul_pow`"

VisualLevelNumber "14"

namespace MyNat

Introduction
"
The music gets ever more dramatic, as we explore
the interplay between exponentiation and multiplication.
"

/-- `mul_pow a b n` is a proof that $(ab)^n=a^nb^n.$ -/
TheoremDoc MyNat.mul_pow as "mul_pow" in "^"

Statement mul_pow : ∀ a b n : ℕ, (a * b) ^ n = a ^ n * b ^ n := by
  exact fun a b n => by
    induction n with t ht
    · rw [pow_zero, pow_zero, pow_zero, mul_one]
    · rw [pow_succ, pow_succ, pow_succ, ht, mul_assoc, mul_assoc, mul_comm (b ^ t) (a * b),
        mul_assoc, mul_comm b (b ^ t)]
