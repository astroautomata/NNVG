import Game.Levels.LessOrEqual.L03_ZeroLe

World "LessOrEqual"
Level 4

Title "Successor is Increasing"

VisualLevelNumber "3"

namespace MyNat

Introduction
"
If you build the wrong number, you get stuck with a goal you can't prove.
What number will you build here?
"

/-- `le_succ_self n` is a proof that `n ≤ S n`. -/
TheoremDoc MyNat.le_succ_self as "le_succ_self" in "≤"

Statement le_succ_self : ∀ n : ℕ, n ≤ S n := by
  exact fun n => by
    rw [← add_one]
    exact (⟨1, reflection _⟩ : ∃ c, n + 1 = n + c)

Conclusion
"
This works because `add_one n` is a proof of `n + 1 = S n`.
"
