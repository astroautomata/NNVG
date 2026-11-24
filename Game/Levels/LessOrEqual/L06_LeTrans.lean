import Game.Levels.LessOrEqual.L05_ExistsHyp

World "LessOrEqual"
Level 6

Title "Transitivity"

VisualLevelNumber "5"

namespace MyNat

Introduction
"
Two inequalities as hypotheses. {pc: Click | mobile: Tap} `hxy` to take it apart.
"

/--
`le_trans x y z` is a proof that if `x ≤ y` and `y ≤ z` then `x ≤ z`.
More precisely, it is a proof that `x ≤ y → (y ≤ z → x ≤ z)`. In words,
If $x \le y$ then (pause) if $y \le z$ then $x \le z$.

## A note on associativity

In Lean, `a + b + c` means `(a + b) + c`, because `+` is left associative. However
`→` is right associative. This means that `x ≤ y → y ≤ z → x ≤ z` in Lean means
exactly that `≤` is transitive. This is different to how mathematicians use
$P \implies Q \implies R$; for them, this usually means that $P \implies Q$
and $Q \implies R$.
-/
TheoremDoc MyNat.le_trans as "le_trans" in "≤"

Statement le_trans (x y z : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  exact (hxy : ∃ c, y = x + c).elim (fun a ha => (hyz : ∃ c, z = y + c).elim (fun b hb =>
    (⟨a + b, by rw [hb, ha, add_assoc]⟩ : ∃ c, z = x + c)))

Conclusion
"
A passing mathematician remarks that with reflexivity and transitivity out of the way,
you have proved that `≤` is a *preorder* on `ℕ`.
"
