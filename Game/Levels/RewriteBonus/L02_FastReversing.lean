import Game.Metadata

World "RewriteBonus"
Level 2

Title "Fast Reversing"

VisualLevelNumber "A1"
VisualRewriteOnly

Statement (a b : ℕ) (a_plus_b : a + b = b) (b_plus_a : a = b + a) :
    a + b + a + b + a = a := by
  rw [a_plus_b, ← b_plus_a, a_plus_b, ← b_plus_a]

VisualTransformText "{pc: You can right-click anywhere on the lower menu to swap substitution directions. | mobile: You can swipe left or right on the lower menu to set the substitution direction.}"
