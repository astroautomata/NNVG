import Game.Levels.AdvMultiplication.L09_MulRightEqSelf

World "AdvMultiplication"
Level 10

Title "`mul_left_cancel` (Advanced Multiplication World Boss)"

VisualLevelNumber "9"
VisualBossLevel

namespace MyNat

Introduction
"
In this level we prove that if `a ≠ 0` and `a * b = a * c` then `b = c`. There is no
induction to lean on here, but `≤` World's boss says that `b ≤ c` or `c ≤ b`. Either
way one of the two numbers is the other plus some `d`, and then `a * d = 0`.
"

/-- `mul_left_cancel a b c` is a proof that if `a ≠ 0` and `a * b = a * c` then `b = c`. -/
TheoremDoc MyNat.mul_left_cancel as "mul_left_cancel" in "*"

Statement mul_left_cancel : ∀ a b c : ℕ, a ≠ 0 → a * b = a * c → b = c := by
  exact fun a b c ha h => (leq_total b c).elim
    (fun hbc => (hbc : ∃ d, c = b + d).elim (fun d hd => by
      rw [hd, ((mul_eq_zero a d (add_right_eq_self (a * b) (a * d) (by rw [hd, mul_add] at h; exact h.symm))).elim
        (fun h0 => (ha h0).elim) (fun h0 => h0) : d = 0), add_zero]))
    (fun hcb => (hcb : ∃ d, b = c + d).elim (fun d hd => by
      rw [hd, ((mul_eq_zero a d (add_right_eq_self (a * c) (a * d) (by rw [hd, mul_add] at h; exact h))).elim
        (fun h0 => (ha h0).elim) (fun h0 => h0) : d = 0), add_zero]))
