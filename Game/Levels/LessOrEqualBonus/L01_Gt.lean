import Game.Levels.LessOrEqualBoss

World "LessOrEqualBonus"
Level 1

Title "`>`"

VisualLevelNumber "A0"

VisualGoalInfo above false "We define `a > b` as `¬ (a ≤ b)`."

namespace MyNat

Introduction
"
`a > b` means `¬ (a ≤ b)`, and `a < b` means `b > a`. A number's successor is greater
than the number.
"

/-- `lt_succ_self a` is a proof of `S a > a`, which is the same as `a < S a`. -/
TheoremDoc MyNat.lt_succ_self as "lt_succ_self" in "≤"

Statement lt_succ_self : ∀ a : ℕ, S a > a := by
  exact fun a => by
    rw [← add_one_eq_succ]
    exact fun h => (h : ∃ c, a = a + 1 + c).elim (fun c hc =>
      one_ne_zero (add_right_eq_zero 1 c (add_right_eq_self a (1 + c) (by rw [← add_assoc]; exact hc.symm))))
