import Game.Levels.LessOrEqualJoined.L01_LeZero

World "LessOrEqualJoined"
Level 2

Title "`≤` Add Right Cancel"

VisualLevelNumber "7"

namespace MyNat

Introduction
"
Adding the same number to both sides of an inequality changes nothing, so it can be
taken away again: if `x + n ≤ y + n` then `x ≤ y`.
"

/-- `leq_add_right_cancel x y n` is a proof that if `x + n ≤ y + n` then `x ≤ y`. -/
TheoremDoc MyNat.leq_add_right_cancel as "leq_add_right_cancel" in "≤"

Statement leq_add_right_cancel : ∀ x y n : ℕ, x + n ≤ y + n → x ≤ y := by
  exact fun x y n h => (h : ∃ c, y + n = x + n + c).elim (fun c hc => (⟨c, add_right_cancel y (x + c) n
    (by rw [add_assoc, add_comm c n, ← add_assoc]; exact hc)⟩ : ∃ c, y = x + c))
