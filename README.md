# Natural Numbers Video Game

A Lean 4 game built for Visual Lean's drag-and-drop interface. It needs a
lean4game (`../lean4game`) with the level-format features it uses, which its `main`
has. The spec lives in `../../NNVG_plans`.

## Layout

- `Game/Levels/Intro`: the welcome text (a `VisualTextLevel`) before the map splits.
- `Game/Levels/Rewrite`: Rewrite World, played entirely in Rewrite Mode (`VisualRewriteOnly`).
- `Game/Levels/RewriteBonus`: bonus levels A0 (Fast Rewriting) and A1 (Fast Reversing), branching off Rewrite World level 2 (`VisualBonusOf Rewrite 3`).
- `Game/Levels/RewriteBonusB`: bonus level B0 (Fixed Point), a second branch off the same level; neither bonus needs the other.
- `Game/Levels/Proposition`: Proposition World up to level 7, played on the canvas.
- `Game/Levels/PropositionRight`: Proposition World from level 8 to the boss, level 15, the right branch of its fork (`VisualContinues Proposition`).
- `Game/Levels/PropositionBonus`: bonus level A0, branching off level 9.
- `Game/Levels/PropositionBonusB`: bonus levels B0 to B2 (the other De Morgan's law), branching off the boss.
- `Game/Levels/PropositionBonusC`: bonus level C0 about the Law of Excluded Middle (¬¬LEM), a second branch off the boss; neither bonus needs the other. (The two branches have traded letters twice: the Lean worlds keep their letters and trade their levels.) Both lead on to Logic World and name its column (`VisualMapColumn 3`), so their paths join into one.
- `Game/Levels/Successor`: Successor World's levels 0 to 2, up to its first boss, in Rewrite Mode.
- `Game/Levels/SuccessorJoined`: Successor World past the barrier, where Proposition World's left branch joins it (`VisualContinues Successor`): Crossing the Beams (0) and (1), levels 3 and 4, and the boss, level 5.
- `Game/Levels/Induction`: Induction World's levels 0 to 3, after Successor World: `zero_add` to `add_assoc`. From its level 0 on in the spec, a goal's variables are under a `∀` and fixed by clicking the goal, unless a hypothesis of the level is about them: the ≠ World, Multiplication and Exponentiation World, ≤ World and Advanced Multiplication World state their levels that way too (`Statement foo : ∀ a b : ℕ, …`, with the reference proof starting `exact fun a b => by …`).
- `Game/Levels/Neq`: the ≠ World's levels 0 to 8, after Successor World and all of Proposition World. Level 3, The Third Mode?, walks through Specialization Mode with `reflection`, level 4 is `succ_inj`, and level 5, Pattern Matching, drags it straight onto a hypothesis `S a = S b` three times over. Level 7 is `one_ne_zero`; `zero_ne_one` is a plain theorem beside it that level 8, `2 ≠ 3`, unlocks.
- `Game/Levels/NeqJoined`: the ≠ World's boss, level 9, Zero or No Zero, which also needs Induction World's first part (`VisualContinues Neq`).
- `Game/Levels/InductionJoined`: Induction World's levels 4 to 7, which wait for the ≠ World (`VisualContinues Induction`): `add_right_cancel`, `add_right_eq_self`, Zero or No Zero?, which brings the cases card, and `add_right_eq_zero` (a miniboss, with a hint for the branch whose goal `S(a1) = 0` can't be true). A theorem's numbers are named on its card as in its level (`add_right_cancel` keeps NNG4's `a`, `b` and `n`, which Visual Lean fills in by name). The mirror images `add_left_cancel` and `add_left_eq_self` have no levels: they are plain theorems, unlocked with the level they sit beside. The swap button is back here.
- `Game/Levels/InductionDouble`: Induction World's levels 8 and 9: Double Induction (`a + a = b + b → a = b`) and the boss, decidable equality. A Lean world of its own from when ≤ World waited for level 7 and again for level 9; it waits for level 9 alone now.
- `Game/Levels/Multiplication`, `Power`, `PowerBonus`, `LessOrEqual`, `LessOrEqualJoined`, `LessOrEqualBoss`, `AdvMultiplication`: the worlds ported from NNG4, with Visual Lean's gestures in place of the typed tactics in their text. Multiplication and Exponentiation World hangs off Induction World's level 3 on the far left: levels 0 to 7 are about multiplication (`Multiplication`; `add_mul` is a plain theorem that `mul_add` unlocks, and `mul_assoc` a miniboss), levels 8 to 16 about powers (`Power`, which `VisualContinues Multiplication`; the boss is FOILed Again, `add_sq`). Refute Fermat's Last Theorem? is a bonus boss off it: the statement without the numbers being positive, `∀ a b c n, n > 2 → a ^ n + b ^ n ≠ c ^ n`, is the premise and `False` the goal (`0 ^ 3 + 0 ^ 3 = 0 ^ 3`). It is stated with `>` (`a > b` is `¬ a ≤ b`), so it also waits for ≤ World's bonus levels about `>` (`Dependency LessOrEqualBonus → PowerBonus`: the path carries that bonus row on and turns down onto it, and the locked level's tooltip says “needs ≤ World Bonus”); its level goes to the right of the path (`VisualBonusSide right`). ≤ World follows the ≠ World on the right: levels 0 to 5 (`LessOrEqual`; 0 is `∃ n, n + n = 0`, 4 is `∃` Hypotheses), 6 to 9 once all of Induction World is done (`LessOrEqualJoined`; 7 is `≤` Add Right Cancel, `leq_add_right_cancel`) and the boss, level 10 (`LessOrEqualBoss`, a Lean world of its own from when it alone waited for the end of Induction World). `LessOrEqualBonus` is four bonus levels about `>` off the boss, sent to the left (`VisualBonusSide left`): A0 `S a > a` (`lt_succ_self`), A1 irreflexivity, A2 transitivity, A3 trichotomy. `add_left_eq_zero` is a plain theorem that ≤ World's level 1 gives; it is proved there from scratch, since that part of ≤ World doesn't wait for `add_right_eq_zero`. Advanced Multiplication World (levels 0 to 9) carries on below ≤ World and also needs Multiplication and Exponentiation World's level 7, whose path comes across from the far left. It allows no `cases` or `induction`: `peano_cases` (level 1) gives the two forms of a number, and the boss, `mul_left_cancel`, compares `b` and `c` with `le_total`.
- `Game/Levels/Logic`: Logic World, one level so far, labelled A0 (the Law of Excluded Middle is equivalent to double negation elimination), after both of Proposition World's last bonus branches and the ≠ World. Nothing follows it.
- `Game/Levels/Outro`: The End, the closing text level at the bottom of the map (`VisualMapBottom`), after the final bosses of Multiplication and Exponentiation World and Advanced Multiplication World.
- `Game/MyNat/Definition.lean`: the game's own natural numbers `MyNat` (`ℕ`), as in NNG4, with the successor named `S`.
- `Game/MyNat/Fraction.lean`: the small `ℚ` that the fraction levels use.
- `Game/MyNat/Induction.lean`: `induction n with n1 hn1`, which Visual Lean plays, without Mathlib.
- `Game/MyNat/Multiplication.lean`, `Power.lean`, `LE.lean`: `*` and `^` as in NNG4 (two axioms each), and `≤`: `a ≤ b` is `∃ c, b = a + c`, as in NNG4, kept semireducible so cards show `≤`; `a > b` is `¬ a ≤ b`. `VisualNumberedWitnesses` in `Game/Metadata.lean` names the numbers that `≤` hypotheses give `c1`, `c2`, ….
- `Game/Tactic/Cases.lean`: `cases n with n1`, which Visual Lean plays, without Mathlib.
- `test/VisualMoves.lean`: replays the levels' solutions with Visual Lean's tactics.

Each world is a column of levels on the path map (`VisualPathMap` in `Game.lean`).
Map labels come from `VisualLevelNumber`, so levels show as 0, 1, 2, … and the
bonuses as A0, A1, B0, …, while Lean numbers them from 1.

A Lean world is one unbroken chain of levels, so a named world that other paths join or
leave partway is split into several Lean worlds, joined with `Dependency` and
`VisualContinues`. A level's map node, title and unlocking all follow from that. It's
also why the player returns to the map at a fork: it's the end of a Lean world.

## Conventions

- `VisualNeutralPalette` in `Game.lean` gives the game its look, which has one scheme (no light and dark mode, white text): the map is a blackboard's slate, and inside a world the page and its panels are a muted tone of the world's own, and everything coloured is the world's. A world has five colours (what is finished, what the player acts with, theorem cards, tactic cards, what the player assumed or derived in the level) and one for what is still to do (an open goal, Rewrite Mode's check mark, open branches), for now the same orange in every world; hints are grey. `VisualWorldColor <scheme>` in a world file names the world's scheme, after the spec's reference image for it: `lantern` (Rewriting World), `aqueduct` (Proposition World), `signal` (Successor World), `blossom` (Induction World), `riverside` (the ≠ World), `sandstone` (Multiplication World), `circuit` (≤ World), `canyon` (Advanced Multiplication World) and `frost` (Logic World). A world without one is played on the map's slate, in greys (only the opening and The End, which are text), and a bonus or a continuation takes its world's: the levels about powers are `sandstone` like the rest of Multiplication and Exponentiation World. The map's menu has a "Visual Style" setting with three choices: Standard is this look, Standard Black is the same with every background black, and High Contrast draws the whole game in Visual Lean's classic dark colours, as it was before this look. In High Contrast each scheme's world has a plain colour on the map (amber for `lantern`, and so on). The same menu has "Full Complete", which shows every level as finished and unlocked without touching the saved progress. The colours themselves are in lean4game's `client/src/visual/palette.css`; `NNG2/palette-picker` edits them.
- `VisualTypeColumn` in `Game.lean` keeps a level's variables in a column of their own at the left of the canvas, where they can be reordered but not dragged out (tactics are still dropped on them), and puts the Proof tab beside Reset and Undo. A `∀` hypothesis is specialized by clicking it, not by dragging a variable onto it.
- `VisualPersistentHints` in `Game.lean` keeps a hint up after the state it was written for, until the next hint, and after the level is finished; write `VisualGoalInfoOnGoal … while …` for one that leaves with its goal, or a hint with empty text to clear.
- `VisualRewriteCheck` shows Rewrite Mode's check mark on goals in every level, not only Rewrite-only ones. Clicking it closes the goal and takes the player back to Proposition Mode.
- `VisualGoalInfoOtherwise above false "…"` is a hint for every state that none of the level's other goal hints is written for (≤ World's level 0: any witness but the right one).
- `VisualSuccessorName S` names the successor in the specialization view's term builder.
- `VisualHideSwapSides` in a world file hides Rewrite Mode's swap-sides button (`a = b` to `b = a`) in all of that world's levels: Rewrite World and its bonuses, Proposition World and its bonuses, Successor World, Induction World's levels 0 to 3 and Multiplication and Exponentiation World. The ≠ World has it, and so does Induction World once the ≠ World has merged back in (levels 4 on).
- Rewrite Mode's tabs: `VisualNoRewriteTabs` (a world or a level) leaves them out, so every rule is in one list (Rewrite World, its bonuses, and Successor World 1); `VisualNoHypothesesTab` leaves out the Hypotheses tab alone (Successor World 2 and 3, which have no hypotheses); `VisualStartTab "+"` picks the tab a level opens on (`"Hypotheses"` for that one).
- `VisualTacticUses`: `cases` and `induction` are only for the levels that say so. `Game.lean` gives both a count of 0 for every level (the cards show `x0` and are greyed out), and a world or level file gives the count the spec states: `VisualTacticUses induction 1` in Induction World's first part and in Multiplication and Exponentiation World, 2 in Induction World's last two levels, and level by level elsewhere (`induction` once in Induction World's levels 4 and 5 and in the ≠ World's boss, twice in ≤ World's; `cases` once in Induction World's level 6 and ≤ World's level 9 and twice in Induction World's level 7). A use counts on its branch and the branches that come from it. While a use is left on the branch being worked on, the Tactics tab glows.
- `VisualNumberedSplits` in `Game.lean`: `cases` or `induction` on `a` names the new number `a1` (so the successor case reads `S(a1)`) and the inductive hypothesis `ha1`; splitting `a1` gives `a2`. Hints that quote such goals use those names.
- Hint text can differ by device: `{pc: … | mobile: …}` (bonus A2's hint is about right-clicking the lower menu on a PC and swiping it on a phone, either of which sets the substitution direction).
- A hint line `[Click to reveal: …]` or `[Click to show: …]` is a button with that label that shows the rest when pressed.
- `VisualNoRewriteMode` in a level refuses Rewrite Mode on the goal with a warning, so the equality is proved like any proposition (the first ≠ World levels). Rewrite Mode on a hypothesis stays available.
- `VisualTransformSwapInfoOnHypothesis "1 = x" show "…"` is a Rewrite Mode hint with an arrow to the swap button.
- Every level shows its variables, like `A : Prop` and `x : ℕ`, as cards.
- The inventory's tabs are NNG4's (`+`, `*`, `^`, `≤`, `012`, `Peano`): file a theorem with `TheoremDoc … in "+"`. There is no Axioms tab; `VisualAxioms` in `Game.lean` lists the theorems shown with the axioms' double border in Rewrite Mode. A level's own hypotheses are grey there, as on the canvas.
- A click on a goal `a = a` closes it, as does the check mark in Rewrite Mode. (`VisualNoGoalRfl` in `Game.lean` would refuse the click; the game no longer uses it.)
- A numbered series of levels counts from zero, as in `Implications (0)`, `(1)`, `(2)`.
- A world's final boss has its world in its title, as in `Plug and Chug (Successor World Boss)`. Other boss levels (`VisualBossLevel`) keep a plain title. No title has a chili pepper.
- A variable named `frac1over2` displays as a vertical fraction.
- A name ending in `_inv`, like `a_inv`, displays with `⁻¹`.
- Reference proofs use only `rw`, `exact`, `induction`, `cases` and term mode, so that `MakeGame` doesn't warn about what no world introduces: an `∃` goal is proved with `exact (⟨c, …⟩ : ∃ c, …)` and a `≤` hypothesis taken apart with `(h : ∃ c, y = x + c).elim fun c hc => …` (not `match`, a literal `Exists.elim` or an explicit `S`, which all count as used and unintroduced). What a reference proof uses also makes its world depend on the world that introduces it, so ≤ World's levels 0 to 5 use nothing from Induction World's levels 4 on. Where a level allows no `cases` or `induction`, its reference proof uses none either (Advanced Multiplication World, ≤ World's levels 0 to 8), which shows the level can be done.
- The ported worlds keep NNG4's theorem names, but `succ` is `S`, there is no `add_right_comm`, and `add_one_eq_succ : a + 1 = S a` stands in for `succ_eq_add_one`. They introduce no typed tactics (`use`, `left`, `right`, `have`, `tauto`, `exfalso`, `symm`): the visual gestures do those jobs.

## Build and play locally

```bash
lake build                          # writes .lake/gamedata
lake env lean test/VisualMoves.lean # silent when every move works
cd ../lean4game && npm start        # then open http://localhost:3000/g/local/NNVG/visual
```

`npm start` runs the native relay, so Lean (v4.28.0, via elan) must be on the PATH.
