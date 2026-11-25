import Game.Levels.LessOrEqualJoined.L02_LeAddRightCancel

World "LessOrEqualJoined"
Level 3

Title "Antisymmetry of `≤`"

VisualLevelNumber "8"

namespace MyNat

Introduction
"
This level asks you to prove *antisymmetry* of $\\leq$.
In other words, if $a \\leq b$ and $b \\leq a$ then $a = b$.
It's the trickiest one so far. Good luck!
"

/-- `leq_antisymm a b` is a proof that if `a ≤ b` and `b ≤ a` then `a = b`. -/
TheoremDoc MyNat.leq_antisymm as "leq_antisymm" in "≤"

Statement leq_antisymm (a b : ℕ) (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  exact (hab : ∃ c, b = a + c).elim (fun d hd => (hba : ∃ c, a = b + c).elim (fun e he => by
    rw [hd, add_right_eq_zero d e (add_right_eq_self a (d + e) (by rw [← add_assoc, ← hd]; exact he.symm)),
      add_zero]))

Conclusion
"
A passing mathematician remarks that with antisymmetry as well,
you have proved that `≤` is a *partial order* on `ℕ`.

The boss level of this world is to prove that `≤` is a total order.
"
