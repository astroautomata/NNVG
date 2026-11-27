import Game.Levels.LessOrEqual.L03_ZeroLe

World "LessOrEqual"
Level 4

Title "Addition is Increasing"

VisualLevelNumber "3"

VisualTacticUses induction 1

-- Experimental (V13.2): the screen after the level.
VisualPostLevel "Proposition Unlocked!"
VisualPostLevelUnlock leq_right_add_self "Adding natural numbers can only make them larger."

namespace MyNat

Introduction
"
If you build the wrong number, you get stuck with a goal you can't prove.
What number will you build here?
"

/-- `leq_right_add_self a n` is a proof that `a ≤ a + n`. -/
TheoremDoc MyNat.leq_right_add_self as "leq_right_add_self" in "≤"

Statement leq_right_add_self : ∀ a n : ℕ, a ≤ a + n := by
  exact fun a n => (⟨n, reflection _⟩ : ∃ c, a + n = a + c)
