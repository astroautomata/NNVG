import Game.Metadata

World "PropositionRight"
Level 2

Title "Disjunction (2)"

VisualLevelNumber "9"

Statement (A B : Prop) : (A ∨ B) → (B ∨ A) := by
  exact fun h => h.elim .inr .inl

VisualGoalInfoOnGoal above false "A ∨ B → B ∨ A" show
  "$∨$ hypotheses can be split by {pc: clicking | mobile: tapping} on them.
In order to finish the proof, you'll have to show that the goal is reachable from both sides!"

VisualGoalInfoOnGoalWithHyp above false "B ∨ A" "A ∨ B" show
  "$∨$ hypotheses can be split by {pc: clicking | mobile: tapping} on them.
In order to finish the proof, you'll have to show that the goal is reachable from both sides!"

-- Splitting the `∨` goal while the `∨` hypothesis is still whole.
VisualGoalInfoOnGoalWithHyp above false "B" "A ∨ B" show
  "Whether to pick $A$ or $B$ will depend on which branch of the $∨$ hypothesis we're in.
So this is a dead end: try undoing or resetting with the buttons on the bottom left!"

VisualGoalInfoOnGoalWithHyp above false "A" "A ∨ B" show
  "Whether to pick $A$ or $B$ will depend on which branch of the $∨$ hypothesis we're in.
So this is a dead end: try undoing or resetting with the buttons on the bottom left!"

-- Past the split of the hypothesis: the side this branch has no proof of.
VisualGoalInfoOnGoalWithHyp above false "B" "A" show
  "We don't have any way of proving $B$ in this branch, so this is a dead end.
Try undoing or resetting with the buttons on the bottom left!"

VisualGoalInfoOnGoalWithHyp above false "A" "B" show
  "We don't have any way of proving $A$ in this branch, so this is a dead end.
Try undoing or resetting with the buttons on the bottom left!"

-- Once the hypothesis is split, the goal still has to be reached in each branch. Said
-- for these states themselves, so that it holds whichever branch was looked at last.
VisualGoalInfoOnGoalWithHyp above false "B ∨ A" "A" show
  "$∨$ hypotheses can be split by {pc: clicking | mobile: tapping} on them.
In order to finish the proof, you'll have to show that the goal is reachable from both sides!"

VisualGoalInfoOnGoalWithHyp above false "B ∨ A" "B" show
  "$∨$ hypotheses can be split by {pc: clicking | mobile: tapping} on them.
In order to finish the proof, you'll have to show that the goal is reachable from both sides!"

-- The side this branch does have a proof of: nothing to warn about, whatever was said
-- in the other branch.
VisualGoalInfoOnGoalWithHyp above false "A" "A" show ""
VisualGoalInfoOnGoalWithHyp above false "B" "B" show ""
