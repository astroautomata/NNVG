import Game.Levels.InductionJoined.L03_ZeroOrNot

World "InductionJoined"
Level 4

Title "`add_right_eq_zero` (Miniboss)"

VisualLevelNumber "7"
VisualBossLevel

VisualTacticUses cases 2

-- A branch whose goal can't be true: `S(…) = 0`, or the other way round once swapped.
-- These are the ones two uses of `cases` lead to. Each hint leaves with its goal.
VisualGoalInfoOnGoal above false "S(a1) = 0" while
  "Sometimes proof branch goals are clearly impossible.
This means that the case must be impossible.
Use your hypotheses to create a hypothesis `False` which can solve even impossible goals!"
VisualGoalInfoOnGoal above false "0 = S(a1)" while
  "Sometimes proof branch goals are clearly impossible.
This means that the case must be impossible.
Use your hypotheses to create a hypothesis `False` which can solve even impossible goals!"
VisualGoalInfoOnGoal above false "S(S(a2)) = 0" while
  "Sometimes proof branch goals are clearly impossible.
This means that the case must be impossible.
Use your hypotheses to create a hypothesis `False` which can solve even impossible goals!"
VisualGoalInfoOnGoal above false "0 = S(S(a2))" while
  "Sometimes proof branch goals are clearly impossible.
This means that the case must be impossible.
Use your hypotheses to create a hypothesis `False` which can solve even impossible goals!"

namespace MyNat

Introduction
"
If `a + b = 0` then `a = 0` and `b = 0`. Let's prove the first of these facts in this
level. `≤` World builds on it.

Dragging `cases` onto `b` deals with `b = 0` and `b = S b1` separately.
"

/--  A proof that $a+b=0 \implies a=0$. -/
TheoremDoc MyNat.add_right_eq_zero as "add_right_eq_zero" in "+"

Statement add_right_eq_zero : ∀ a b : ℕ, a + b = 0 → a = 0 := by
  exact fun a b => by
    cases b with d
    · exact fun h => by rw [add_zero] at h; exact h
    · exact fun h => (zero_ne_succ (a + d) (by rw [add_succ] at h; exact h.symm)).elim
