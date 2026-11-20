import Game.Levels.Neq.L07_Ne

World "Neq"
Level 8

Title "`one_ne_zero`"

VisualLevelNumber "7"

namespace MyNat

Introduction
"
Peano's last axiom is `zero_ne_succ a`, a proof that `0 ≠ S a`: zero is not the
successor of any number.
"

/-- `zero_ne_succ a` is a proof of `0 ≠ S a`, which means `0 = S a → False`. -/
TheoremDoc MyNat.zero_ne_succ as "zero_ne_succ" in "Peano"

NewTheorem MyNat.zero_ne_succ
VisualEmphasize MyNat.zero_ne_succ

/-- `one_ne_zero` is a proof of `1 ≠ 0`. -/
TheoremDoc MyNat.one_ne_zero as "one_ne_zero" in "012"

Statement one_ne_zero : (1 : ℕ) ≠ 0 := by
  rw [one_eq_succ_zero]
  exact fun h => zero_ne_succ 0 h.symm

Conclusion
"
Completing this level also unlocks `zero_ne_one`, a proof of `0 ≠ 1`.
"
