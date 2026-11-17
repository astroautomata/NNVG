import Game.Metadata

World "PropositionRight"
Level 6

Title "Negation (2)"

VisualLevelNumber "12"

Statement (A B : Prop) : A → ¬B → ¬(A → B) := by
  exact fun hA hNotB hAB => hNotB (hAB hA)
