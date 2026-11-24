import Game.Levels.Induction.L01_ZeroAdd
import Game.Levels.Induction.L02_SuccAdd
import Game.Levels.Induction.L03_AddComm
import Game.Levels.Induction.L04_AddAssoc

World "Induction"
Title "Induction World"

VisualWorldColor blossom
VisualMapColumn -1

-- Rewrite Mode's swap-sides button is hidden in these levels, 0 to 3: it comes back
-- once the ≠ World has merged in (`InductionJoined`).
VisualHideSwapSides

-- One induction per branch of a proof: the tactic shows `x1`, then `x0` in the base
-- case, the inductive step and whatever comes from them. (`Game.lean` allows none where
-- a world or level doesn't say.)
VisualTacticUses induction 1

Introduction
"
Prove the basic properties of addition by induction.
"
