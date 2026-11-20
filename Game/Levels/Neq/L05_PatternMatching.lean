import Game.Levels.Neq.L04_ThirdMode

World "Neq"
Level 5

Title "Pattern Matching"

VisualLevelNumber "4"

namespace MyNat

Statement : S 0 = S 0 ∧ ((1 : ℕ) = 1 ∧ ((2 : ℕ) + 2) + 2 = (2 + 2) + 2) := by
  exact ⟨reflection _, reflection _, reflection _⟩

-- Dragging `reflection` onto a goal `a = a` specializes it to match.
VisualGoalInfo above false
  "Try dragging `reflection` straight to the goal to automatically match it."
