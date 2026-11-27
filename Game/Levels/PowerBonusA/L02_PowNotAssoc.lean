import Game.Levels.PowerBonusA.L01_PowNotComm

World "PowerBonusA"
Level 2

Title "Exponentiation is Not Associative"

VisualLevelNumber "A1"

namespace MyNat

Introduction
"
`(a + b) + c = a + (b + c)` and `(a * b) * c = a * (b * c)`, but with powers it matters
where the brackets are.

Assume it didn't, and find three numbers for which that is absurd.
"

-- As in the level before, the general statement is the premise and `False` the goal.
Statement : (∀ a b c : ℕ, (a ^ b) ^ c = a ^ (b ^ c)) → False := by
  exact fun h => one_ne_zero (by rw [← pow_zero (0 ^ 0), h 0 0 0, zero_pow_zero, pow_one])

Conclusion
"
`(0 ^ 0) ^ 0 = 1`, but `0 ^ (0 ^ 0) = 0 ^ 1 = 0`.
"
