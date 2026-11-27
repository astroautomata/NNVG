import Game.Metadata

World "PropositionRight"
Level 4

Title "The Principle of Explosion"

VisualLevelNumber "11"

-- Experimental (V13.2): the screen before the level. The spec gives `False` no other name.
VisualPreLevel "Symbol Unlocked!"
VisualPreLevelSymbol "False" "" "Often denoted `⊥` or `Absurd`, `False` is the proposition that must never be allowed to exist. Intuitionistic logic is built on the idea that you must never be able to construct a proof of `False`. Because if you could prove `False`, you could prove anything at all.

Handle with care."
VisualHideRewriteDirection

Statement (h : False) : (1 : ℕ) = 2 := by
  exact h.elim

VisualGoalInfo above false
  "A ‘False’ hypothesis can prove *anything*!"
