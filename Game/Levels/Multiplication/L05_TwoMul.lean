import Game.Levels.Multiplication.L04_MulComm

World "Multiplication"
Level 5

Title "`two_mul`"

VisualLevelNumber "4"

-- No induction in this level.
VisualTacticUses induction 0

-- Experimental (V13.2): the screen after the level.
VisualPostLevel "Equality Unlocked!"
VisualPostLevelUnlock two_mul "Multiplying a number by two is just adding a number with itself."

namespace MyNat

Introduction
"
This level is more important than you think; it plays
a useful role when battling a big boss later on.
"

/--
`two_mul m` is the proof that `2 * m = m + m`.
-/
TheoremDoc MyNat.two_mul as "two_mul" in "*"

-- Unlocked by completing `mul_comm` (the level before).
NewTheorem MyNat.one_mul

Statement two_mul : ∀ m : ℕ, 2 * m = m + m := by
  exact fun m => by rw [two_eq_succ_one, succ_mul, one_mul]
