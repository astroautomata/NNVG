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

/-- `le_succ_self x` is a proof that `x ≤ S x`. -/
TheoremDoc MyNat.le_succ_self as "le_succ_self" in "≤"

Statement le_succ_self : ∀ x : ℕ, x ≤ S x := by
  exact fun x => by
    rw [← add_one_eq_succ]
    exact (⟨1, reflection _⟩ : ∃ c, x + 1 = x + c)

Conclusion
"
This works because `add_one_eq_succ x` is a proof of `x + 1 = S x`.
"
