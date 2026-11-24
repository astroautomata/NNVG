import Game.Levels.InductionJoined.L01_AddRightCancel
import Game.Levels.InductionJoined.L02_AddRightEqSelf
import Game.Levels.InductionJoined.L03_ZeroOrNot
import Game.Levels.InductionJoined.L04_AddRightEqZero

World "InductionJoined"
Title "Induction World"

-- Induction World past its barrier, levels 4 to 7: it needs the ≠ World finished too.
-- The swap-sides button is back. Each level says which of `induction` and `cases` it
-- allows, and how often.
VisualContinues Induction
VisualMapColumn -1

Introduction
"
More about addition, now that implications and `≠` are around: cancellation, and what
it takes for a sum to be zero.
"
