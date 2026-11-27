import Game.Levels.Power
import Game.Levels.Neq

World "PowerBonusA"
Level 1

Title "Exponentiation is Not Commutative"

VisualLevelNumber "A0"

namespace MyNat

Introduction
"
Addition and multiplication don't care about the order of their numbers. Powers do:
`a ^ b` and `b ^ a` are usually different.

To show it, assume they were always equal, and find two numbers for which that is absurd.
"

-- As in the level about Fermat, the general statement is the premise and `False` the
-- goal.
Statement : (∀ a b : ℕ, a ^ b = b ^ a) → False := by
  exact fun h => zero_ne_one (by rw [← pow_one 0, h 0 1, pow_zero])

Conclusion
"
`0 ^ 1 = 0`, but `1 ^ 0 = 1`.
"
