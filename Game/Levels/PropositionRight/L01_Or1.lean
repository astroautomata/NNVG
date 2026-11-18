import Game.Metadata

World "PropositionRight"
Level 1

Title "Disjunction (1)"

VisualLevelNumber "8"

Statement (A B C : Prop) (hB : B) : A ∨ (B ∨ C) := by
  exact .inr (.inl hB)

VisualGoalInfoOnGoal above false "A ∨ B ∨ C" show
  "The symbol $∨$ represents ‘or’. In order to prove an ‘or’ goal, you must choose to prove either the left side or the right side.
Be careful not to get stuck in a dead end!"

VisualGoalInfoOnGoal above false "A" show
  "We don't have any way of proving $A$, so this is a dead end.
Try undoing or resetting with the buttons on the bottom left!"

VisualGoalInfoOnGoal above false "C" show
  "We don't have any way of proving $C$, so this is a dead end.
Try undoing or resetting with the buttons on the bottom left!"

-- Back on the way through, whatever was said in a dead end.
VisualGoalInfoOnGoal above false "B ∨ C" show
  "The symbol $∨$ represents ‘or’. In order to prove an ‘or’ goal, you must choose to prove either the left side or the right side.
Be careful not to get stuck in a dead end!"

VisualGoalInfoOnGoal above false "B" show ""
