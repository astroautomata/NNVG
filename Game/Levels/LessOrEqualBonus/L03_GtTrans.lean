import Game.Levels.LessOrEqualBonus.L02_GtIrrefl

World "LessOrEqualBonus"
Level 3

Title "Transitivity of `>`"

VisualLevelNumber "A2"

namespace MyNat

Introduction
"
If `a > b` and `b > c` then `a > c`. `≤` World's boss says how `b` and `c` compare.
"

Statement : ∀ a b c : ℕ, a > b → b > c → a > c := by
  exact fun a b c hab hbc hac => (le_total b c).elim (fun h => hbc h) (fun h => hab (leq_trans a c b hac h))
