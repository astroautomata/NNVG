import Game.Metadata

World "PropositionBonusB"
Level 1

Title "¬¬LEM"

VisualLevelNumber "B1"

Statement : ∀ P : Prop, ¬¬(P ∨ ¬P) := by
  exact fun _ h => h (.inr (fun p => h (.inl p)))

VisualGoalInfo above false
  "It's not possible to prove the Law of Excluded Middle in intuitionistic logic.
($∀ P, P ∨ ¬P$)
However, it *is* possible to show you can't *refute* the Law of Excluded Middle."
