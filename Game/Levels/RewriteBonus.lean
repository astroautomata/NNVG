import Game.Levels.RewriteBonus.L01_FastRewriting
import Game.Levels.RewriteBonus.L02_FastReversing

World "RewriteBonus"
Title "Rewrite World Bonus"

-- Sprouts off Rewrite World after its level 2 (Lean level 3); not needed to continue.
-- Bonus B (`RewriteBonusB`) leaves the same level.
VisualBonusOf Rewrite 3

-- Rewrite World's bonuses are played like Rewrite World: no swap-sides button.
VisualHideSwapSides

-- No tabs under the rules: every rule of a level is in one list.
VisualNoRewriteTabs

Introduction
"
Bonus puzzles. You don't need them to continue along Rewrite World.
"
