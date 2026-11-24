import Game.Levels.LessOrEqualJoined.L03_LeAntisymm

World "LessOrEqualJoined"
Level 4

Title "`le_one`"

VisualLevelNumber "9"

VisualTacticUses cases 1

namespace MyNat

Introduction
"
We've seen `le_zero`, the proof that if `x ≤ 0` then `x = 0`.
Now we'll prove that if `x ≤ 1` then `x = 0` or `x = 1`.
"

/-- `le_one x` is a proof that if `x ≤ 1` then `x = 0` or `x = 1`. -/
TheoremDoc MyNat.le_one as "le_one" in "≤"

Statement le_one (x : ℕ) (hx : x ≤ 1) : x = 0 ∨ x = 1 := by
  cases x with d
  · exact .inl (reflection 0)
  · rw [← add_one_eq_succ] at hx
    exact (hx : ∃ c, 1 = d + 1 + c).elim (fun c hc => .inr (by
      rw [add_right_eq_zero d c (succ_inj (d + c) 0 (by
          rw [add_assoc, add_comm 1 c, ← add_assoc, add_one_eq_succ, one_eq_succ_zero] at hc; exact hc.symm)),
        one_eq_succ_zero]))

Conclusion
"
If you solved this level then you are ready for the boss!
"
