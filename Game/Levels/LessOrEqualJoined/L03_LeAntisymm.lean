import Game.Levels.LessOrEqualJoined.L02_LeAddRightCancel

World "LessOrEqualJoined"
Level 3

Title "Antisymmetry"

VisualLevelNumber "8"

namespace MyNat

Introduction
"
This level asks you to prove *antisymmetry* of $\\leq$.
In other words, if $x \\leq y$ and $y \\leq x$ then $x = y$.
It's the trickiest one so far. Good luck!
"

/-- `le_antisymm x y` is a proof that if `x ≤ y` and `y ≤ x` then `x = y`. -/
TheoremDoc MyNat.le_antisymm as "le_antisymm" in "≤"

Statement le_antisymm (x y : ℕ) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  exact (hxy : ∃ c, y = x + c).elim (fun a ha => (hyx : ∃ c, x = y + c).elim (fun b hb => by
    rw [ha, add_right_eq_zero a b (add_right_eq_self x (a + b) (by rw [← add_assoc, ← ha]; exact hb.symm)),
      add_zero]))

Conclusion
"
A passing mathematician remarks that with antisymmetry as well,
you have proved that `≤` is a *partial order* on `ℕ`.

The boss level of this world is to prove that `≤` is a total order.
"
