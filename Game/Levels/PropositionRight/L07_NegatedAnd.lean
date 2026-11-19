import Game.Metadata

World "PropositionRight"
Level 7

Title "Negation (2)"

VisualLevelNumber "14"

Statement (A B : Prop) : A → ¬(A ∧ B) → ¬B := by
  exact fun hA hNotAB hB => hNotAB ⟨hA, hB⟩

VisualGoalInfo above false
  "Hint:
[Click to reveal: Remember that you can rewrite backwards from the goal!]"
