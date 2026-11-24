import Game.MyNat.Multiplication

/-!
# Powers

Exponentiation of the game's natural numbers, as in NNG4: opaque, with the two axioms
`pow_zero` and `pow_succ` as its only definition. Note that `0 ^ 0 = 1`.
-/

namespace MyNat

/-- Exponentiation of natural numbers. Opaque, so Lean never computes `2 ^ 3` to `8`. -/
opaque pow : MyNat → MyNat → MyNat

instance instPow : Pow MyNat MyNat where
  pow := pow

-- `a ^ b` with numerals, such as `2 ^ 3`, elaborates with both sides in `MyNat`.
macro_rules | `($x ^ $y) => `(HPow.hPow ($x : MyNat) ($y : MyNat))

/-- `pow_zero a` is a proof of `a ^ 0 = 1`. -/
axiom pow_zero (a : MyNat) : a ^ 0 = 1

/-- `pow_succ a b` is a proof of `a ^ S b = a ^ b * a`. -/
axiom pow_succ (a b : MyNat) : a ^ S b = a ^ b * a

end MyNat
