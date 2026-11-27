import Game.Levels.PowerBonusA.L01_PowNotComm
import Game.Levels.PowerBonusA.L02_PowNotAssoc

World "PowerBonusA"
Title "Multiplication and Exponentiation World Bonus"

-- Bonus A, off `pow_pow` (level 14): powers are neither commutative nor associative.
-- Not needed to continue. Both levels end at `0 = 1` or `1 = 0`, so they also need the
-- ≠ World's `zero_ne_one` and `one_ne_zero`.
VisualBonusOf Power 8
-- The map draws no path for that: it would cross the whole map from the ≠ World. A
-- locked level says what it needs.
VisualNoPathFrom Neq
VisualNoPathFrom NeqJoined
VisualHideSwapSides

Introduction
"
Two bonus levels about what powers don't do. You don't need them to continue.
"
