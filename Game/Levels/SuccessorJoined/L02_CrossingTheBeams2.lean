import Game.Levels.SuccessorJoined.L01_CrossingTheBeams

World "SuccessorJoined"
Level 2

Title "Crossing the Beams (1)"

VisualLevelNumber "5"

namespace MyNat

-- A hypothesis is opened in Rewrite Mode: `hx` is rewritten into `x = 2`, which is
-- what `hy` asks for.
Statement (x y : ℕ) (hx : x = 1 + 1) (hy : x = 2 → y = 0) : y = 0 := by
  rw [add_one_eq_succ, ← two_eq_succ_one] at hx
  exact hy hx

VisualHypInfoOnHyp hx "x = 1 + 1" show
  "We can also enter hypotheses in Rewriting Mode.
Try {pc: double-clicking | mobile: double-tapping} `hx` to edit it."

VisualTransformInfoOnHypothesis "x = 1 + 1" show
  "We need to match the form `x = 2`."

VisualTransformBackInfoOnHypothesis "x = 2" show
  "We can return back to Proposition Mode by {pc: clicking | mobile: tapping} ‘Back’."
