import Game.Levels.Neq.L05_SuccInj

World "Neq"
Level 6

Title "Pattern Matching"

VisualLevelNumber "5"

namespace MyNat

Statement (x y : ℕ) (h : S (S (S x)) = S (S (S y))) : x = y := by
  exact succ_inj _ _ (succ_inj _ _ (succ_inj _ _ h))

-- Dragging `succ_inj` onto a hypothesis `S a = S b` specializes it to match.
VisualGoalInfo above false
  "Try dragging `succ_inj` straight onto `h` to automatically apply it."
