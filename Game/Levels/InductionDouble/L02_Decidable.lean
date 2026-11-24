import Game.Levels.InductionDouble.L01_DoubleInduction

World "InductionDouble"
Level 2

Title "Equality in ℕ is Decidable (Induction World Boss)"

VisualLevelNumber "9"
VisualBossLevel

-- The hint stays up (hints persist in this game) until induction has been done twice
-- the right way round: fix `a`, induct on it, fix `b`, induct on it. Each hint below
-- with no text matches one of the four goals that leaves, and clears it. In the two
-- `S(a1)` cases the inductive hypothesis has to hold for every `b`, which it doesn't if
-- `b` was fixed before the induction on `a`.
VisualGoalInfoOnGoal above false "∀ (a b : ℕ), a = b ∨ a ≠ b" show
  "Don’t forget to apply double induction properly!"
VisualGoalInfoOnGoal above false "0 = 0 ∨ 0 ≠ 0" show ""
VisualGoalInfoOnGoal above false "0 = S(b1) ∨ 0 ≠ S(b1)" show ""
VisualGoalInfoOnGoalWithHyp above false "S(a1) = 0 ∨ S(a1) ≠ 0" "∀ (b : ℕ), a1 = b ∨ a1 ≠ b" show ""
VisualGoalInfoOnGoalWithHyp above false "S(a1) = S(b1) ∨ S(a1) ≠ S(b1)" "∀ (b : ℕ), a1 = b ∨ a1 ≠ b" show ""
-- If `b` was fixed first, the zero case can still be finished, which clears the hint, but
-- the `S(a1)` case is stuck with a hypothesis about that one `b`: the hint comes back.
VisualGoalInfoOnGoalWithHyp above false "S(a1) = b ∨ S(a1) ≠ b" "a1 = b ∨ a1 ≠ b" show
  "Don’t forget to apply double induction properly!"

namespace MyNat

Statement : ∀ a b : ℕ, a = b ∨ a ≠ b := by
  exact fun a => by
    induction a with d hd
    · exact fun b => by
        induction b with e he
        · exact .inl (reflection 0)
        · exact .inr (zero_ne_succ e)
    · exact fun b => by
        induction b with e he
        · exact .inr (fun h => zero_ne_succ d h.symm)
        · exact (hd e).elim (fun h => .inl (by rw [h])) (fun h => .inr (fun h2 => h (succ_inj d e h2)))
