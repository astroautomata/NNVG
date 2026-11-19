import Game.Metadata

World "PropositionRight"
Level 6

Title "Negation (1)"

VisualLevelNumber "13"

Statement (A B : Prop) : A → ¬B → ¬(A → B) := by
  exact fun hA hNotB hAB => hNotB (hAB hA)
