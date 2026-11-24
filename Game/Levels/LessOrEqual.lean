import Game.Levels.LessOrEqual.L01_Exists
import Game.Levels.LessOrEqual.L02_LeRefl
import Game.Levels.LessOrEqual.L03_ZeroLe
import Game.Levels.LessOrEqual.L04_LeSuccSelf
import Game.Levels.LessOrEqual.L05_ExistsHyp
import Game.Levels.LessOrEqual.L06_LeTrans

World "LessOrEqual"
Title "≤ World"

-- Levels 0 to 5, after the ≠ World. The rest waits for Induction World (`LessOrEqualJoined`
-- for its level 7, `LessOrEqualBoss` for its last).
VisualWorldColor circuit
VisualMapColumn 1

Introduction
"
In this world we define `a ≤ b` and prove standard facts
about it, such as \"if `a ≤ b` and `b ≤ c` then `a ≤ c`.\"

The definition of `a ≤ b` is \"there exists a number `c`
such that `b = a + c`. \" So we're going to have to learn
how to prove \"exists\" statements, and how to use \"exists\" hypotheses.
"
