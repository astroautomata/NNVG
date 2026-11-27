import Game.Levels.LessOrEqualJoined.L03_LeAntisymm

World "LessOrEqualJoined"
Level 4

Title "`leq_one`"

VisualLevelNumber "10"

VisualTacticUses cases 1

namespace MyNat

Introduction
"
We've seen `leq_zero`, the proof that if `n ≤ 0` then `n = 0`.
Now we'll prove that if `n ≤ 1` then `n = 0` or `n = 1`.
"

/-- `leq_one n` is a proof that if `n ≤ 1` then `n = 0` or `n = 1`. -/
TheoremDoc MyNat.leq_one as "leq_one" in "≤"

Statement leq_one (n : ℕ) (hn : n ≤ 1) : n = 0 ∨ n = 1 := by
  cases n with d
  · exact .inl (reflection 0)
  · rw [← add_one] at hn
    exact (hn : ∃ c, 1 = d + 1 + c).elim (fun c hc => .inr (by
      rw [add_right_eq_zero d c (succ_inj (d + c) 0 (by
          rw [add_assoc, add_comm 1 c, ← add_assoc, add_one, one_eq_succ_zero] at hc; exact hc.symm)),
        one_eq_succ_zero]))

Conclusion
"
If you solved this level then you are ready for the boss!
"
