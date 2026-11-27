import Game.Levels.Multiplication

World "Power"
Level 1

Title "`zero_pow_zero`"

VisualLevelNumber "7"

-- No induction in this level.
VisualTacticUses induction 0

-- Experimental (V13.2): the screen before the level, in two pages (the symbol, then the
-- axiom), and the one after it.
VisualPreLevel "Symbol Unlocked!"
VisualPreLevelSymbol "^" "Exponentiation" "`a ^ b` means raising `a` to the power of `b`. The caret stands in for a proper superscript."
VisualPreLevel "Axiom Equality Unlocked!"
VisualPreLevelUnlock pow_zero "Any number to the zeroth power is one."
VisualPostLevel "Equality Unlocked!"
VisualPostLevelUnlock zero_pow_zero "Counter-intuitively, zero to the zeroth power is one."

namespace MyNat

Introduction
"
Mathematicians sometimes debate what `0 ^ 0` is;
the answer depends, of course, on your definitions. In this
game, `0 ^ 0 = 1`. See if you can prove it.

Check out the new axiom `pow_zero` in your inventory.
"

/--
`Pow a b`, with notation `a ^ b`, is the usual exponentiation of natural numbers.
Internally it is defined via two axioms:

* `pow_zero a : a ^ 0 = 1`

* `pow_succ a b : a ^ S b = a ^ b * a`

Note in particular that `0 ^ 0 = 1`.
-/
DefinitionDoc Pow as "^"

NewDefinition Pow

/--
`pow_zero a : a ^ 0 = 1` is one of the two axioms
defining exponentiation in this game.
-/
TheoremDoc MyNat.pow_zero as "pow_zero" in "^"

/--
Mathematicians sometimes argue that `0 ^ 0 = 0` is also
a good convention. But it is not a good convention in this
game; all the later levels come out beautifully with the
convention that `0 ^ 0 = 1`.
-/
TheoremDoc MyNat.zero_pow_zero as "zero_pow_zero" in "^"

-- The axiom is introduced on the screen before the level, with no glow here.
NewTheorem MyNat.pow_zero

Statement zero_pow_zero : (0 : ℕ) ^ 0 = 1 := by
  rw [pow_zero]
