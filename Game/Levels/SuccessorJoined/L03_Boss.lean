import Game.Levels.SuccessorJoined.L02_CrossingTheBeams2

World "SuccessorJoined"
Level 3

Title "Plug and Chug (Successor World Boss)"

VisualLevelNumber "5"
VisualBossLevel

namespace MyNat

Statement (a b c : ℕ) (ha : a = 0 + 0 + 0) (hb : S (0 + 0) = b) (hc : c = b + (a + a) + 0) :
    c + c + c + c = 4 := by
  rw [add_zero, add_zero] at ha
  rw [add_zero, ← one_eq_succ_zero] at hb
  rw [add_zero, ha, add_zero, add_zero, ← hb] at hc
  rw [hc, add_one_eq_succ, add_one_eq_succ, add_one_eq_succ, four_eq_succ_three,
    three_eq_succ_two, two_eq_succ_one]

VisualGoalInfo above false
  "Hint:
[Click to show: Try simplifying the hypotheses before editing the goal.]"
