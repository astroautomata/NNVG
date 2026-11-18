import Game.Levels.Neq
import Game.Levels.Induction

World "NeqJoined"
Level 1

Title "Zero or No Zero"

VisualLevelNumber "8"

namespace MyNat

/-- `eq_or_neq_zero n` is a proof of `n = 0 ∨ n ≠ 0`. -/
TheoremDoc MyNat.eq_or_neq_zero as "eq_or_neq_zero" in "012"

Statement eq_or_neq_zero : ∀ n : ℕ, n = 0 ∨ n ≠ 0 := by
  exact fun n => by
    induction n with d hd
    · exact .inl (reflection 0)
    · exact .inr (fun h => zero_ne_succ d h.symm)
