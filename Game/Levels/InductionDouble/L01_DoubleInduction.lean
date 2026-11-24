import Game.Levels.InductionJoined

World "InductionDouble"
Level 1

Title "Double Induction"

VisualLevelNumber "8"

-- The opening hint stays up (hints persist in this game) while `a` is fixed, which is
-- still the right way round. Fixing `b` as well before the induction on `a` is the dead
-- end: the inductive hypothesis is then about that one `b`, and its hint stays up for
-- whatever the player tries from there. After the induction on `a` with `b` still
-- under its `∀`, the two hints with no text clear what was up.
VisualGoalInfoOnGoal above false "∀ (a b : ℕ), a + a = b + b → a = b" show
  "Some proofs will require applying induction more than once.
To do this properly, we need to make our inductive hypothesis as general as possible.
Here, try inducting on `a` BEFORE introducing `b`!"
VisualGoalInfoOnGoal above false "a + a = b + b → a = b" show
  "This is a dead end: you must apply induction on `a` before introducing `b` in order to generalize the inductive hypothesis!"
VisualGoalInfoOnGoal above false "∀ (b : ℕ), 0 + 0 = b + b → 0 = b" show ""
VisualGoalInfoOnGoal above false "∀ (b : ℕ), S(a1) + S(a1) = b + b → S(a1) = b" show ""

namespace MyNat

Introduction
"
If `a + a = b + b` then `a = b`. Induction on `a` alone is not enough: the step for
`S a` needs the inductive hypothesis at the number before `b`, so it has to hold for
every `b`.
"

Statement : ∀ a b : ℕ, a + a = b + b → a = b := by
  exact fun a => by
    induction a with d hd
    · exact fun b => by
        induction b with e he
        · exact fun _ => reflection 0
        · exact fun h => (zero_ne_succ _ (by rw [add_zero, add_succ] at h; exact h)).elim
    · exact fun b => by
        induction b with e he
        · exact fun h => (zero_ne_succ _ (by rw [add_zero, add_succ] at h; exact h.symm)).elim
        · exact fun h => by
            rw [hd e (succ_inj (d + d) (e + e) (succ_inj _ _
              (by rw [add_succ, add_succ, succ_add, succ_add] at h; exact h)))]
