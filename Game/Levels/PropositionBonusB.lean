import Game.Levels.PropositionBonusB.L01_Leftwards
import Game.Levels.PropositionBonusB.L02_ExcludedMiddle
import Game.Levels.PropositionBonusB.L03_WeakExcludedMiddle

World "PropositionBonusB"
Title "Proposition World Bonus"

-- Sprouts off Proposition World's boss, level 15 (Lean level 8). Bonus C
-- (`PropositionBonusC`) leaves the same level; neither needs the other. Both lead on to
-- Logic World, down one path in its column.
VisualBonusOf PropositionRight 8
VisualMapColumn 3
VisualHideSwapSides

Introduction
"
Bonus puzzles about the other De Morgan's law. You don't need them to continue.
"
