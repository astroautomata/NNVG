import Game.Levels.LessOrEqualJoined
import Game.Levels.InductionDouble

World "LessOrEqualBoss"
Level 1

Title "`≤` is Total (≤ World Boss)"

VisualLevelNumber "10"
VisualBossLevel

VisualTacticUses induction 2

namespace MyNat

Introduction
"
This is I think the toughest level yet. Tips: dragging `induction` onto a number `a`
splits into the cases `a = 0` and `a = S a1`, whether or not you need the inductive
hypothesis. And don't choose a side of an `∨` goal until your hypotheses guarantee that
you can prove it!
"

/-- `le_total x y` is a proof that `x ≤ y` or `y ≤ x`. -/
TheoremDoc MyNat.le_total as "le_total" in "≤"

Statement le_total : ∀ x y : ℕ, x ≤ y ∨ y ≤ x := by
  exact fun x y => by
    induction y with d hd
    · exact .inr (zero_le x)
    · exact hd.elim (fun h1 => .inl (le_trans x d _ h1 (le_succ_self d)))
        (fun h2 => (h2 : ∃ c, x = d + c).elim (fun e he => by
          induction e with a _ha
          · exact .inl (by rw [add_zero] at he; rw [he]; exact le_succ_self d)
          · exact .inr (by
              rw [← add_one_eq_succ]
              exact (⟨a, by rw [add_assoc, add_comm 1 a, add_one_eq_succ]; exact he⟩ :
                ∃ c, x = d + 1 + c))))

Conclusion
"
Very well done.

A passing mathematician remarks that you've just proved that `ℕ` is totally
ordered.
"
