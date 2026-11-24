import Game.Levels.Neq.L06_PatternMatching

World "Neq"
Level 7

Title "`≠`"

VisualLevelNumber "6"

namespace MyNat

Introduction
"
`a ≠ b` means `a = b → False`.
"

Statement : ∀ x y : ℕ, (S x = S y ∧ x ≠ y) → False := by
  exact fun x y h => h.2 (succ_inj x y h.1)

VisualGoalInfo above false
  "`x ≠ y` simply means `¬ x = y`"
