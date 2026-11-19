import Game.Metadata

World "PropositionRight"
Level 5

Title "Negation (0)"

VisualLevelNumber "12"

Statement (A : Prop) (hA : A) : ¬¬A := by
  exact fun hNotA => hNotA hA

VisualGoalInfo above false
  "$¬A$ just means $A → False$!"
