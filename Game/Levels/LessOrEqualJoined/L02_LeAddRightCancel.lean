import Game.Levels.LessOrEqualJoined.L01_LeZero

World "LessOrEqualJoined"
Level 2

Title "`≤` Add Right Cancel"

VisualLevelNumber "7"

namespace MyNat

Introduction
"
Adding the same number to both sides of an inequality changes nothing, so it can be
taken away again: if `a + n ≤ b + n` then `a ≤ b`.
"

/-- `leq_add_right_cancel a b n` is a proof that if `a + n ≤ b + n` then `a ≤ b`. -/
TheoremDoc MyNat.leq_add_right_cancel as "leq_add_right_cancel" in "≤"

Statement leq_add_right_cancel : ∀ a b n : ℕ, a + n ≤ b + n → a ≤ b := by
  exact fun a b n h => (h : ∃ c, b + n = a + n + c).elim (fun c hc => (⟨c, add_right_cancel b (a + c) n
    (by rw [add_assoc, add_comm c n, ← add_assoc]; exact hc)⟩ : ∃ c, b = a + c))
