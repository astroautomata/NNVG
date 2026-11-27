import Game.Metadata

World "Proposition"
Level 8

Title "If and Only If (Conjunctions)"

VisualLevelNumber "7"

-- Experimental (V13.2): the screen before the level.
VisualPreLevel "Symbol Unlocked!"
VisualPreLevelSymbol "↔" "If and Only If" "`A ↔ B` means that `A → B` and `B → A`.

In other words, wherever A or B are true, both are true."

Statement (A B C : Prop) : ((A ∧ B) ∧ C) ↔ (A ∧ (B ∧ C)) := by
  exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

VisualGoalInfoOnGoal above false "(A ∧ B) ∧ C ↔ A ∧ B ∧ C" show
  "$A ↔ B$ just means $(A → B) ∧ (B → A)$.
{pc: Click | mobile: Tap} it to separate just like $∧$!"
