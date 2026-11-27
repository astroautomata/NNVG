import Game.Levels.Successor.L02_AddOne

World "Successor"
Level 3

Title "Counting to Four (Miniboss)"

VisualLevelNumber "2"

VisualRewriteOnly
VisualNoHypothesesTab
-- `add_one` is in the `+` tab.
VisualStartTab "+"
VisualBossLevel
VisualEmphasize MyNat.add_one

namespace MyNat

Statement : (1 : ℕ) + 1 + 1 + 1 = 4 := by
  rw [add_one, add_one, add_one, four_eq_succ_three, three_eq_succ_two,
    two_eq_succ_one]
