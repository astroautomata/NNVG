import GameServer
import Game.MyNat.Definition
import Game.MyNat.Fraction
import Game.MyNat.Induction
import Game.MyNat.Multiplication
import Game.MyNat.Power
import Game.MyNat.LE
import Game.Tactic.Cases

-- The number a click takes out of a hypothesis `a ≤ b` is named `c1`, `c2`, …, never
-- plain `c`. Here, not in `Game.lean`: every level imports this file.
VisualNumberedWitnesses

/-- `rw [h]` rewrites the goal with the equality `h`, replacing its left side by its
right side. `rw [← h]` rewrites from right to left. -/
TacticDoc rw

/-- `exact h` closes the goal with `h`, whose type must be exactly the goal. -/
TacticDoc exact

/-- `induction n with n1 hn1` attempts to prove the goal by induction on `n`, with the
inductive variable in the successor case being `n1`, and the inductive hypothesis
being `hn1`.

If the goal is `0 + n = n`, it turns into two goals. The first is `0 + 0 = 0`; the second
has an assumption `hn1 : 0 + n1 = n1` and goal `0 + S n1 = S n1`. -/
TacticDoc induction
