import Game.Metadata

World "PropositionRight"
Level 5

Title "Negation (0)"

VisualLevelNumber "12"

-- Experimental (V13.2): the screen before the level.
VisualPreLevel "Symbol Unlocked!"
VisualPreLevelSymbol "¬" "Negation (Not)" "`¬A` means that `A → False`. In other words, were `A` to exist, we could prove `False`, which is catastrophic."

Statement (A : Prop) (hA : A) : ¬¬A := by
  exact fun hNotA => hNotA hA

VisualGoalInfo above false
  "$¬A$ just means $A → False$!"
