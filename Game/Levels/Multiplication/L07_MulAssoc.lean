import Game.Levels.Multiplication.L06_MulAdd

World "Multiplication"
Level 7

Title "`mul_assoc` (Miniboss)"

VisualLevelNumber "6"
VisualBossLevel

-- Experimental (V13.2): the screen after the level.
VisualPostLevel "Equality Unlocked!"
VisualPostLevelUnlock mul_assoc "Like addition, multiplication is associative."
VisualPostLevelText "Now having established multiplication, we can move on to exponentiation!"

namespace MyNat

Introduction
"
We now have enough to prove that multiplication is associative. Good luck!
"

/--
`mul_assoc a b c` is a proof that `(a * b) * c = a * (b * c)`.

Note that when Lean says `a * b * c` it means `(a * b) * c`.

Note that `(a * b) * c = a * (b * c)` cannot be proved by \"pure thought\":
for example subtraction is not associative, as `(6 - 2) - 1` is not
equal to `6 - (2 - 1)`.
-/
TheoremDoc MyNat.mul_assoc as "mul_assoc" in "*"

-- Unlocked by completing Distributivity (the level before).
NewTheorem MyNat.add_mul

Statement mul_assoc : ∀ a b c : ℕ, (a * b) * c = a * (b * c) := by
  exact fun a b c => by
    induction c with d hd
    · rw [mul_zero, mul_zero, mul_zero]
    · rw [mul_succ, mul_succ, hd, mul_add]

Conclusion
"
A passing mathematician notes that you've proved
that the natural numbers are a commutative semiring.

Powers are next, on the way to the final boss.
"
