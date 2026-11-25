import Game.Levels.Successor.L01_Successor

World "Successor"
Level 2

Title "`add_one`"

VisualLevelNumber "1"

-- Experimental (V13): the screens before and after the level.
VisualPreLevel "Axioms Unlocked!"
VisualPreLevelUnlock add_zero "Eliminate added zeroes, but only on the right."
VisualPreLevelUnlock add_succ "Move successor functions out to the right addend."
VisualPostLevel "Theorem Unlocked!"
VisualPostLevelUnlock add_one "Quickly collapse added ones."
VisualPostLevelText "Many proofs you complete will be available to you as theorems that you can use in all future levels.

This will allow us to prove increasingly sophisticated results!"
VisualRewriteOnly
-- There are no hypotheses before level 3.
VisualNoHypothesesTab

namespace MyNat

/-- `add_zero n` is a proof of `n + 0 = n`. -/
TheoremDoc MyNat.add_zero as "add_zero" in "+"

/-- `add_succ a b` is a proof of `a + S b = S (a + b)`. -/
TheoremDoc MyNat.add_succ as "add_succ" in "+"

NewTheorem MyNat.add_zero MyNat.add_succ

/-- `add_one a` is a proof of `a + 1 = S a`. -/
TheoremDoc MyNat.add_one as "add_one" in "+"

Statement add_one (a : ℕ) : a + 1 = S a := by
  rw [one_eq_succ_zero, add_succ, add_zero]

VisualTransformText "In this world, we'll prove all the basic properties of addition from only the axioms below (and induction)!"
