import Game.Levels.LessOrEqualBonus.L01_Gt

World "LessOrEqualBonus"
Level 2

Title "Irreflexivity of `>`"

VisualLevelNumber "A1"

namespace MyNat

Introduction
"
No number is greater than itself.
"

Statement : ∀ a : ℕ, ¬ (a > a) := by
  exact fun a h => h (le_refl a)
