import Game.Levels.Induction.L02_SuccAdd

World "Induction"
Level 3

Title "Commutativity of Addition"

VisualLevelNumber "2"

-- Experimental (V13): the screen after the level.
VisualPostLevel "Theorem Unlocked!"
VisualPostLevelUnlock add_comm "Allows you to swap added terms.

We say a binary operation is *commutative* if its terms can be freely swapped without changing the result."

namespace MyNat

Introduction
"
Look in your inventory to see the proofs you have available.
These should be enough.
"

/-- `add_comm x y` is a proof of `x + y = y + x`. -/
TheoremDoc MyNat.add_comm as "add_comm" in "+"

Statement add_comm : ∀ a b : ℕ, a + b = b + a := by
  exact fun a b => by
    induction b with d hd
    · rw [add_zero, zero_add]
    · rw [add_succ, succ_add, hd]
