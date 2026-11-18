import Game.Metadata

World "PropositionRight"
Level 4

Title "The Principle of Explosion"

VisualLevelNumber "11"
VisualHideRewriteDirection

Statement (h : False) : (1 : ℕ) = 2 := by
  exact h.elim

VisualGoalInfo above false
  "A ‘False’ hypothesis can prove *anything*!"
