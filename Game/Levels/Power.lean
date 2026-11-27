import Game.Levels.Power.L01_ZeroPowZero
import Game.Levels.Power.L02_ZeroPowSucc
import Game.Levels.Power.L03_PowOne
import Game.Levels.Power.L04_OnePow
import Game.Levels.Power.L05_PowTwo
import Game.Levels.Power.L06_PowAdd
import Game.Levels.Power.L07_MulPow
import Game.Levels.Power.L08_PowPow
import Game.Levels.Power.L09_AddPowTwo

World "Power"
Title "Multiplication and Exponentiation World"

-- Multiplication and Exponentiation World's levels 7 to 15, the ones about powers.
VisualContinues Multiplication
VisualMapColumn -2

-- Rewrite Mode's swap-sides button is hidden throughout this world.
VisualHideSwapSides

-- One induction per branch of a proof, in every level that doesn't say otherwise.
VisualTacticUses induction 1

Introduction
"
Now we define powers, `a ^ b`, by two more axioms: `pow_zero a : a ^ 0 = 1`
and `pow_succ a b : a ^ S b = a ^ b * a`. Everything else about powers follows from
these, by induction. The boss of this world is the formula for $(a + b)^2$.
"
