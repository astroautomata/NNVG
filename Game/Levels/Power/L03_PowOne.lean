import Game.Levels.Power.L02_ZeroPowSucc

World "Power"
Level 3

Title "`pow_one`"

VisualLevelNumber "10"

namespace MyNat

/-- `pow_one a` says that `a ^ 1 = a`.

Note that this is not quite true by definition: `a ^ 1` is
defined to be `a ^ 0 * a` so it's `1 * a`, and to prove
that this is equal to `a` you need to use induction somewhere.
-/
TheoremDoc MyNat.pow_one as "pow_one" in "^"

Statement pow_one : ∀ a : ℕ, a ^ 1 = a := by
  exact fun a => by rw [one_eq_succ_zero, pow_succ, pow_zero, one_mul]
