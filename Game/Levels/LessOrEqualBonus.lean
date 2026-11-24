import Game.Levels.LessOrEqualBonus.L01_Gt
import Game.Levels.LessOrEqualBonus.L02_GtIrrefl
import Game.Levels.LessOrEqualBonus.L03_GtTrans
import Game.Levels.LessOrEqualBonus.L04_Trichotomy

World "LessOrEqualBonus"
Title "≤ World Bonus"

-- Sprouts off ≤ World's boss, level 10, to the left; not needed to continue, except
-- for the bonus boss about Fermat, whose path carries this row on.
VisualBonusOf LessOrEqualBoss 1
VisualBonusSide left

Introduction
"
Bonus levels about `>`, which is defined from `≤`. You don't need them to continue.
"
