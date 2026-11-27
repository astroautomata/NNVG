import Game.Levels.LessOrEqual.L01_Exists
import Game.Levels.LessOrEqual.L02_LeRefl
import Game.Levels.LessOrEqual.L03_ZeroLe
import Game.Levels.LessOrEqual.L04_LeRightAddSelf
import Game.Levels.LessOrEqual.L05_ExistsHyp
import Game.Levels.LessOrEqual.L06_LeTrans
import Game.Levels.LessOrEqual.L07_RightAddLe

World "LessOrEqual"
Title "≤ World"

-- Levels 0 to 6, after the ≠ World. The rest waits for all of Induction World
-- (`LessOrEqualJoined`, then the boss in `LessOrEqualBoss`).
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
