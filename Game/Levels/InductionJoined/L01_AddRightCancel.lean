import Game.Levels.Induction
import Game.Levels.NeqJoined

World "InductionJoined"
Level 1

Title "`add_right_cancel`"

VisualLevelNumber "4"

VisualTacticUses induction 1

-- Experimental (V13.1): the screen after the level.
VisualPostLevel "Propositions Unlocked!"
VisualPostLevelUnlock add_right_cancel
VisualPostLevelUnlock add_left_cancel
VisualPostLevelText "Cancel two added terms from either side of an equality."

namespace MyNat

Introduction
"
`add_right_cancel a b n` is the theorem that $a+n=b+n\\implies a=b$.
"

/-- `add_right_cancel a b n` is the theorem that $a+n=b+n \implies a=b.$ -/
TheoremDoc MyNat.add_right_cancel as "add_right_cancel" in "+"

-- Visual Lean fills in `a`, `b` and `n` by those names when a proposition is dropped on
-- the theorem's card. It and its mirror image are unlocked by finishing this level.
Statement add_right_cancel : ∀ a b n : ℕ, a + n = b + n → a = b := by
  exact fun a b n => by
    induction n with d hd
    · exact fun h => by rw [add_zero, add_zero] at h; exact h
    · exact fun h => hd (succ_inj (a + d) (b + d) (by rw [add_succ, add_succ] at h; exact h))

/-- `add_left_cancel a b n` is the theorem that $n+a=n+b \implies a=b.$ -/
TheoremDoc MyNat.add_left_cancel as "add_left_cancel" in "+"

-- The mirror image has no level of its own (`NewTheorem` in the next level).
theorem add_left_cancel (a b n : ℕ) : n + a = n + b → a = b := by
  rw [add_comm n a, add_comm n b]
  exact add_right_cancel a b n

Conclusion
"
Swapping the sides of each sum gives the mirror image, `add_left_cancel`:
if `n + a = n + b` then `a = b`. You have both from now on.
"
