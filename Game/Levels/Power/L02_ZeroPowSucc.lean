import Game.Levels.Power.L01_ZeroPowZero

World "Power"
Level 2

Title "`zero_pow_succ`"

VisualLevelNumber "8"

-- Experimental (V13.2): the screens before and after the level. (The first one's text is
-- the spec's, word for word.)
VisualPreLevel "Axiom Equality Unlocked!"
VisualPreLevelUnlock pow_succ "Exponentiation is repeated multiplication!"
VisualPostLevel "Equality Unlocked!"
VisualPostLevelUnlock zero_pow_succ "In the natural numbers, zero to any power besides zero is zero."

namespace MyNat

Introduction
"
We've just seen that `0 ^ 0 = 1`, but if `n`
is a successor, then `0 ^ n = 0`. We prove that here.
"

/-- `pow_succ a b : a ^ (S b) = a ^ b * a` is one of the
two axioms defining exponentiation in this game.
-/
TheoremDoc MyNat.pow_succ as "pow_succ" in "^"

/--
Although $0^0=1$ in this game, $0^n=0$ if $n>0$, i.e., if
$n$ is a successor.
-/
TheoremDoc MyNat.zero_pow_succ as "zero_pow_succ" in "^"

-- The axiom is introduced on the screen before the level, with no glow here.
NewTheorem MyNat.pow_succ

Statement zero_pow_succ : ∀ n : ℕ, (0 : ℕ) ^ S n = 0 := by
  exact fun n => by rw [pow_succ, mul_zero]
