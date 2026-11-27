import Game.Levels.LessOrEqualJoined
import Game.Levels.InductionDouble

World "LessOrEqualBoss"
Level 1

Title "`≤` is Total (≤ World Boss)"

VisualLevelNumber "11"
VisualBossLevel

-- Experimental (V13.2): the screen after the level.
VisualPostLevel "Proposition Unlocked!"
VisualPostLevelUnlock leq_total "We say a binary operation `·` is *total* if, for any `a, b` on its domain, `a · b` or `b · a`."

VisualTacticUses induction 2

namespace MyNat

Introduction
"
This is I think the toughest level yet. Tips: dragging `induction` onto a number `a`
splits into the cases `a = 0` and `a = S a1`, whether or not you need the inductive
hypothesis. And don't choose a side of an `∨` goal until your hypotheses guarantee that
you can prove it!
"

/-- `leq_total a b` is a proof that `a ≤ b` or `b ≤ a`. -/
TheoremDoc MyNat.leq_total as "leq_total" in "≤"

Statement leq_total : ∀ a b : ℕ, a ≤ b ∨ b ≤ a := by
  exact fun a b => by
    induction b with d hd
    · exact .inr (zero_leq a)
    · rw [← add_one]
      exact hd.elim (fun h1 => .inl (leq_trans a d _ h1 (leq_right_add_self d 1)))
        (fun h2 => (h2 : ∃ c, a = d + c).elim (fun e he => by
          induction e with f _hf
          · exact .inl (by rw [add_zero] at he; rw [he]; exact leq_right_add_self d 1)
          · exact .inr (⟨f, by rw [add_assoc, add_comm 1 f, add_one]; exact he⟩ :
              ∃ c, a = d + 1 + c)))

Conclusion
"
Very well done.

A passing mathematician remarks that you've just proved that `ℕ` is totally
ordered.
"
