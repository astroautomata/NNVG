import Game.Levels.Neq.L06_PatternMatching

World "Neq"
Level 7

Title "`≠`"

VisualLevelNumber "6"

-- Experimental (V13.2): the screen before the level, which says what the level's hint did.
VisualPreLevel "Symbol Unlocked!"
VisualPreLevelSymbol "≠" "Not Equal" "It’s just what it sounds like: `a ≠ b` just means `¬ a = b`.

Some weirdos call these inequations."

namespace MyNat

Introduction
"
`a ≠ b` means `a = b → False`.
"

Statement : ∀ x y : ℕ, (S x = S y ∧ x ≠ y) → False := by
  exact fun x y h => h.2 (succ_inj x y h.1)
