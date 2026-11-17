import Game.Metadata

World "RewriteBonus"
Level 1

Title "Fast Rewriting"

VisualLevelNumber "A1"
VisualRewriteOnly

Statement (zero_add_zero : (0 : ℕ) + 0 = 0) :
    (0 : ℕ) + 0 + 0 + 0 + 0 + 0 + 0 + 0 = 0 := by
  rw [zero_add_zero, zero_add_zero, zero_add_zero, zero_add_zero, zero_add_zero,
    zero_add_zero, zero_add_zero]

VisualTransformText "Instead of dragging hypotheses, you can also {pc: click | mobile: tap} them to make the first substitution possible (reading left to right)."
