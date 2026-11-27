import Game.Levels.LessOrEqualBonus.L03_GtTrans

World "LessOrEqualBonus"
Level 4

Title "`≤` to `>`"

VisualLevelNumber "A3"

VisualTacticUses cases 1

-- Experimental (V13.2): the screen after the level.
VisualPostLevel "Proposition Unlocked!"
VisualPostLevelUnlock leq_le "It’s called ‘less than or equal’ for a reason."

namespace MyNat

Introduction
"
If `a ≤ b`, then the two are equal or `b` is greater. The number that `a ≤ b` gives is
either zero or a successor.
"

/-- `leq_le a b` is a proof that if `a ≤ b` then `a = b` or `b > a`. -/
TheoremDoc MyNat.leq_le as "leq_le" in ">"

Statement leq_le : ∀ a b : ℕ, a ≤ b → a = b ∨ b > a := by
  exact fun a b h => (h : ∃ c, b = a + c).elim (fun c hc => by
    cases c with d
    · exact .inl (by rw [hc, add_zero])
    · rw [← add_one] at hc
      exact .inr (fun hba => (hba : ∃ e, a = b + e).elim (fun e he =>
        one_ne_zero (add_left_eq_zero d 1 (add_right_eq_zero (d + 1) e
          (add_right_eq_self a (d + 1 + e) (by rw [← add_assoc, ← hc]; exact he.symm)))))))
