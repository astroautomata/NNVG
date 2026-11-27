import Game.Metadata

World "Proposition"
Level 2

Title "Implications (0)"

VisualLevelNumber "1"

-- Experimental (V13.2): the screen before the level.
VisualPreLevel "Symbol Unlocked!"
VisualPreLevelSymbol "→" "Implication" "`A → B` means that whenever A is true, B must be true as well."

Statement (A : Prop) : A → A := by
  exact fun h => h

-- With an arrow to the goal, until it is clicked.
VisualGoalInfoOnGoal above true "A → A" while
  "Goals with implications can be {pc: clicked | mobile: tapped} to introduce the left side as a hypothesis and set the right side as the goal."

-- Then an arrow from the introduced `A`, which the click names `h`, to the goal.
VisualHypGoalInfoOnGoal h "A" show
  "Now we can solve the proof by dragging the hypothesis to the goal like before."
