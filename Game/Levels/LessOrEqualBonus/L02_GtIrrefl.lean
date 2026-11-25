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

Statement : ∀ n : ℕ, ¬ (n > n) := by
  exact fun n h => h (leq_refl n)
