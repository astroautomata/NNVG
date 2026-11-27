import Game.Levels.Power.L05_PowTwo

World "Power"
Level 6

Title "`pow_add`"

VisualLevelNumber "12"

-- Experimental (V13.2): the screen after the level.
VisualPostLevel "Equality Unlocked!"
VisualPostLevelUnlock pow_add "Addition in an exponent becomes multiplication when we distribute."

namespace MyNat

Introduction
"
Let's now begin our approach to the final boss,
by proving some more subtle facts about powers.
"

/-- `pow_add a m n` is a proof that $a^{m+n}=a^ma^n.$ -/
TheoremDoc MyNat.pow_add as "pow_add" in "^"

Statement pow_add : ∀ a m n : ℕ, a ^ (m + n) = a ^ m * a ^ n := by
  exact fun a m n => by
    induction n with t ht
    · rw [add_zero, pow_zero, mul_one]
    · rw [add_succ, pow_succ, pow_succ, ht, mul_assoc]
