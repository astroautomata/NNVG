import Game.Levels.LessOrEqual.L05_ExistsHyp

World "LessOrEqual"
Level 6

Title "Transitivity of `≤`"

VisualLevelNumber "5"

namespace MyNat

Introduction
"
Two inequalities as hypotheses. {pc: Click | mobile: Tap} `hxy` to take it apart.
"

/--
`le_trans a b c` is a proof that if `a ≤ b` and `b ≤ c` then `a ≤ c`.
More precisely, it is a proof that `a ≤ b → (b ≤ c → a ≤ c)`. In words,
If $a \le b$ then (pause) if $b \le c$ then $a \le c$.

## A note on associativity

In Lean, `a + b + c` means `(a + b) + c`, because `+` is left associative. However
`→` is right associative. This means that `a ≤ b → b ≤ c → a ≤ c` in Lean means
exactly that `≤` is transitive. This is different to how mathematicians use
$P \implies Q \implies R$; for them, this usually means that $P \implies Q$
and $Q \implies R$.
-/
TheoremDoc MyNat.le_trans as "le_trans" in "≤"

-- The spec keeps the hypotheses' names, `hxy` and `hyz`, with the numbers `a`, `b`, `c`.
Statement le_trans (a b c : ℕ) (hxy : a ≤ b) (hyz : b ≤ c) : a ≤ c := by
  exact (hxy : ∃ d, b = a + d).elim (fun d hd => (hyz : ∃ e, c = b + e).elim (fun e he =>
    (⟨d + e, by rw [he, hd, add_assoc]⟩ : ∃ f, c = a + f)))

Conclusion
"
A passing mathematician remarks that with reflexivity and transitivity out of the way,
you have proved that `≤` is a *preorder* on `ℕ`.
"
