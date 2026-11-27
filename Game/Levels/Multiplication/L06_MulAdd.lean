import Game.Levels.Multiplication.L05_TwoMul

World "Multiplication"
Level 6

Title "Distributivity"

VisualLevelNumber "5"

-- Experimental (V13.2): the screen after the level.
VisualPostLevel "Equalities Unlocked!"
VisualPostLevelUnlock mul_add "Also known as left distributivity."
VisualPostLevelUnlock add_mul "Also known as right distributivity."

namespace MyNat

Introduction
"
Our next goal is \"left and right distributivity\",
meaning $a(b+c)=ab+ac$ and $(b+c)a=ba+ca$. Rather than
these slightly pompous names, the name of the proofs
in Lean are descriptive. Let's start with
`mul_add a b c`, the proof of `a * (b + c) = a * b + a * c`.
Note that the left hand side contains a multiplication
and then an addition.
"

/--
Multiplication distributes
over addition on the left.

`mul_add a b c` is the proof that `a * (b + c) = a * b + a * c`.
-/
TheoremDoc MyNat.mul_add as "mul_add" in "*"

Statement mul_add : ∀ a b c : ℕ, a * (b + c) = a * b + a * c := by
  exact fun a b c => by
    induction c with d hd
    · rw [add_zero, mul_zero, add_zero]
    · rw [add_succ, mul_succ, hd, mul_succ, add_assoc]

/--
`add_mul a b c` is a proof that $(a+b)c=ac+bc$.
-/
TheoremDoc MyNat.add_mul as "add_mul" in "*"

-- The mirror image has no level of its own. Finishing this level unlocks it too
-- (`NewTheorem` in the next one).
theorem add_mul (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, mul_add, mul_comm c a, mul_comm c b]

Conclusion
"
Inducting on `a` or `b` also works, but might take longer.

Its mirror image comes with it: `add_mul`, the proof of `(a + b) * c = a * c + b * c`.
"
