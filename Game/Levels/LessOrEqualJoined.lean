import Game.Levels.LessOrEqualJoined.L01_LeZero
import Game.Levels.LessOrEqualJoined.L02_LeAddRightCancel
import Game.Levels.LessOrEqualJoined.L03_LeAntisymm
import Game.Levels.LessOrEqualJoined.L04_LeOne

World "LessOrEqualJoined"
Title "≤ World"

-- ≤ World past its first barrier, levels 6 to 9: it also needs Induction World up to
-- its level 7 (`InductionJoined`).
VisualContinues LessOrEqual
VisualMapColumn 1

Introduction
"
More facts about `≤`, with the cancellation theorems of Induction World.
"
