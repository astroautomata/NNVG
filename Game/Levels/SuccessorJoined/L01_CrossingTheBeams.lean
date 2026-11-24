import Game.Levels.Successor

World "SuccessorJoined"
Level 1

Title "Crossing the Beams (0)"

VisualLevelNumber "4"
-- Rewrite Mode opens on `hx`.
VisualStartTab "Hypotheses"

namespace MyNat

-- The first level to use Rewriting Mode and Proposition Mode together: the goal is
-- opened in Rewrite Mode, where `hx` is one of the rules.
Statement (x : ℕ) (hx : x = 1) : x + 1 = 2 := by
  rw [hx, add_one_eq_succ, ← two_eq_succ_one]

VisualGoalInfoOnGoal above true "x + 1 = 2" show
  "We will now put Rewriting Mode and Proposition Mode together!
Try {pc: double-clicking | mobile: double-tapping} the goal to open it in Rewriting Mode."

VisualTransformInfoOnGoal "x + 1 = 2" show
  "We can use the hypothesis `hx` to substitute for `x` here."

VisualTransformInfoOnGoal "1 + 1 = 2" show
  "Now we can just make both sides match as usual."
