import Game.Levels.PropositionBonusB.L01_NotNotExcludedMiddle

World "PropositionBonusB"
Level 2

Title "Double Elimination is Equivalent To LEM"

VisualLevelNumber "B2"

/-- `lem_iff_double_elimination` is a proof of `(∀ P, P ∨ ¬P) ↔ (∀ P, ¬¬P → P)`: the
Law of Excluded Middle is equivalent to double negation elimination. -/
TheoremDoc lem_iff_double_elimination as "lem_iff_double_elimination" in "Logic"

Statement lem_iff_double_elimination :
    (∀ P : Prop, P ∨ ¬P) ↔ (∀ P : Prop, ¬¬P → P) := by
  exact ⟨
    fun lem P nnp => (lem P).elim (fun p => p) (fun np => (nnp np).elim),
    fun dne P => dne (P ∨ ¬P) (fun h => h (.inr (fun p => h (.inl p))))⟩
