import Game.Levels.Power
import Game.Levels.LessOrEqualBoss

World "PowerBonus"
Level 1

Title "Refute Fermat's Last Theorem?"

VisualLevelNumber "A1"
VisualBossLevel

namespace MyNat

Introduction
"
Fermat's Last Theorem states that if $x,y,z>0$ and $n > 2$ then $x^n+y^n\\not =z^n$.
Its shortest known proof would translate into many millions of lines of Lean code.

The statement in this level forgot to ask for $x,y,z>0$. That makes all the difference:
it is false, and a few well-chosen numbers show it.

With `≤` World behind us, `n > 2` means `¬ n ≤ 2`.
"

Statement : (∀ a b c n : ℕ, n > 2 → a ^ n + b ^ n ≠ c ^ n) → False := by
  exact fun h => h 0 0 0 3
    (fun h32 => (h32 : ∃ c, (2 : ℕ) = 3 + c).elim (fun c hc => zero_ne_succ (0 + c) (by
      rw [three_eq_succ_two, two_eq_succ_one, succ_add, one_eq_succ_zero, succ_add, succ_add] at hc
      exact succ_inj _ _ (succ_inj _ _ hc))))
    (by rw [three_eq_succ_two, zero_pow_succ, add_zero])

Conclusion
"
Zero to any power above zero is zero, so `0 ^ 3 + 0 ^ 3 = 0 ^ 3`. The real theorem is
safe: it only speaks of positive numbers.

## CONGRATULATIONS!

If you would like to learn more about how to use Lean to
prove theorems in mathematics, then take a look
at [Mathematics In Lean](https://leanprover-community.github.io/mathematics_in_lean/),
an interactive textbook which you can read in your browser,
and which explains how to work with many more mathematical concepts in Lean.
"
