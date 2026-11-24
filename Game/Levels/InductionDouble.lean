import Game.Levels.InductionDouble.L01_DoubleInduction
import Game.Levels.InductionDouble.L02_Decidable

World "InductionDouble"
Title "Induction World"

-- Induction World's last two levels, 8 and 9. They are a Lean world of their own
-- because ≤ World's level 6 waits for level 7 here and its boss for level 9.
VisualContinues InductionJoined
VisualMapColumn -1

-- Double induction: two inductions on each branch of a proof.
VisualTacticUses induction 2

Introduction
"
Some proofs need induction twice, with an inductive hypothesis that holds for every
value of the other variable.
"
