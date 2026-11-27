import Game.Levels.LessOrEqualBoss

World "LessOrEqualBonus"
Level 1

Title "`>`"

VisualLevelNumber "A0"

-- Experimental (V13.2): the screens before and after the level.
VisualPreLevel "Symbol Unlocked!"
VisualPreLevelSymbol ">" "Greater Than" "`a > b` just means that `a` is strictly larger than `b`. We represent this by just negating `≤`: `¬ a ≤ b`."
VisualPostLevel "Proposition Unlocked!"
VisualPostLevelUnlock lt_succ_self "We say a function `f(x)` is *strictly increasing* if x < f(x).

The successor function is strictly increasing."

VisualGoalInfo above false "We define `a > b` as `¬ (a ≤ b)`."

namespace MyNat

Introduction
"
`a > b` means `¬ (a ≤ b)`, and `a < b` means `b > a`. A number's successor is greater
than the number.
"

/-- `lt_succ_self n` is a proof of `S n > n`, which is the same as `n < S n`. -/
TheoremDoc MyNat.lt_succ_self as "lt_succ_self" in ">"

Statement lt_succ_self : ∀ n : ℕ, S n > n := by
  exact fun n => by
    rw [← add_one]
    exact fun h => (h : ∃ c, n = n + 1 + c).elim (fun c hc =>
      one_ne_zero (add_right_eq_zero 1 c (add_right_eq_self n (1 + c) (by rw [← add_assoc]; exact hc.symm))))
