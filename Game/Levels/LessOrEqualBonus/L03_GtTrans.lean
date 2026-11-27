import Game.Levels.LessOrEqualBonus.L02_GtIrrefl

World "LessOrEqualBonus"
Level 3

Title "Transitivity of `>`"

VisualLevelNumber "A2"

-- Experimental (V13.2): the screen after the level.
VisualPostLevel "Proposition Unlocked!"
VisualPostLevelUnlock lt_trans "Like `≤`, `>` is transitive."

namespace MyNat

Introduction
"
If `a > b` and `b > c` then `a > c`. `≤` World's boss says how `b` and `c` compare.
"

/-- `lt_trans a b c` is a proof that if `a > b` and `b > c` then `a > c`. -/
TheoremDoc MyNat.lt_trans as "lt_trans" in ">"

Statement lt_trans : ∀ a b c : ℕ, a > b → b > c → a > c := by
  exact fun a b c hab hbc hac => (leq_total b c).elim (fun h => hbc h) (fun h => hab (leq_trans a c b hac h))
