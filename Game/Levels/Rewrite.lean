import Game.Levels.Rewrite.L01_Substitution
import Game.Levels.Rewrite.L02_ManySubstitutions
import Game.Levels.Rewrite.L03_Backwards
import Game.Levels.Rewrite.L04_GeneralRules
import Game.Levels.Rewrite.L05_Fractions
import Game.Levels.Rewrite.L06_Boss

World "Rewrite"
Title "Rewrite World"

VisualWorldColor lantern
VisualMapColumn -1

-- Rewrite Mode's swap-sides button is hidden throughout this world.
VisualHideSwapSides

-- No tabs under the rules: every rule of a level is in one list.
VisualNoRewriteTabs

Introduction
"
Prove equalities by substituting equal things for each other until both sides match.
"
