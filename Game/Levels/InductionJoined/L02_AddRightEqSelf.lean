import Game.Levels.InductionJoined.L01_AddRightCancel

World "InductionJoined"
Level 2

Title "`add_right_eq_self`"

VisualLevelNumber "5"

VisualTacticUses induction 1

-- Experimental (V13.1): the screen after the level.
VisualPostLevel "Propositions Unlocked!"
VisualPostLevelUnlock add_right_eq_self
VisualPostLevelUnlock add_left_eq_self
VisualPostLevelText "If adding some `b` to a number does not change it, `b` must be zero."

namespace MyNat

Introduction
"
`add_right_eq_self a b` is the theorem that $a + b = a\\implies b=0.$
"

-- Unlocked by completing `add_right_cancel` (the level before).
NewTheorem MyNat.add_left_cancel

/-- `add_right_eq_self a b` is the theorem that $a + b = a \implies b=0.$ -/
TheoremDoc MyNat.add_right_eq_self as "add_right_eq_self" in "+"

Statement add_right_eq_self : ∀ a b : ℕ, a + b = a → b = 0 := by
  exact fun a b => by
    induction a with d hd
    · exact fun h => by rw [zero_add] at h; exact h
    · exact fun h => hd (succ_inj (d + b) d (by rw [succ_add] at h; exact h))

/-- `add_left_eq_self a b` is the theorem that $a + b = b \implies a=0.$ -/
TheoremDoc MyNat.add_left_eq_self as "add_left_eq_self" in "+"

-- The mirror image has no level of its own. Finishing this level unlocks it too
-- (`NewTheorem` in the next one).
theorem add_left_eq_self (a b : ℕ) : a + b = b → a = 0 := by
  exact fun h => add_right_cancel a 0 b (by rw [zero_add]; exact h)

Conclusion
"
Its mirror image comes with it: `add_left_eq_self`, if `a + b = b` then `a = 0`.
"
