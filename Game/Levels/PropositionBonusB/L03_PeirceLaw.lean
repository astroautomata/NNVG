import Game.Levels.PropositionBonusB.L02_DoubleElimination

World "PropositionBonusB"
Level 3

Title "Peirce's Law is Equivalent To LEM"

VisualLevelNumber "B3"

-- The previous level's result, `lem_iff_double_elimination`, is in the inventory: it
-- is a `Statement` with a name, so this level unlocks it.
Statement : (∀ P : Prop, P ∨ ¬P) ↔ (∀ P Q : Prop, ((P → Q) → P) → P) := by
  exact ⟨
    fun lem P Q h => (lem P).elim (fun p => p) (fun np => h (fun p => (np p).elim)),
    fun peirce => lem_iff_double_elimination.mpr
      (fun P nnp => peirce P _ (fun np => (nnp np).elim))⟩
