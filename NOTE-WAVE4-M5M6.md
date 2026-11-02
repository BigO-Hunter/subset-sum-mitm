# Wave 4 report — M5 (scanB) + M6 (budget_compose2) — 2026-11-02

Branch v2-alpha-half: `04ea7fa` (M5), `1b94b13` (merge v2-budget),
`62ddcc6` (M6). All on top of `ef1dc3f` (M4). `lake build Submission`:
Build completed successfully, zero sorry tree-wide.

## M5 — Submission/ScanB.lean (new, 818 lines)

- `scanLoop_exec` — fuel-driven loop walk 238→238, measure
  `(2^(n/2) − i) + jp` (jp = rJ − bd2 = B entries not yet discarded).
  TRUE budget `10 * measure + 2` (j-path 9 steps, i-path 10, accept 9,
  rejectI 11, rejectJ 2). Conclusion: `some false` ∨ (`some true` ∧
  ∃ i' jp' witness `f (bd1+i') + f (bd2+(jp'−1)) = t0`). The witness is
  EXISTENTIAL over (i', jp') — it does NOT tie to the entry indices
  (recursion moves them).
- `scanB_exec` — phase walk 231→verdict, TRUE budget
  `10 * (2^(n/2) + 2^(n−n/2)) + 9` (7 setup + loop; the gap map's +24
  was wrong, landed constant is +9). axioms [propext, Quot.sound].
- `scanB_budget` — same, folded to `30 * 2^(n/2) + 9`.

## Composer-relevant facts (for the final wiring)

1. The loop performs NO stores — the sweep sees the entry memory
   throughout; no `Pres` is needed anywhere in M5.
2. `scanB_exec` hypotheses the composer must supply: register pins
   `f 1=1, f 2=0, f 6=bd1, f 7=n, f 8=2n+23, f 9=n/2, f 11=2^(n−n/2),
   f 19=bd2`, `ht0 : f (3n+24) = t0`, `hbd1/hbd2 : 22 < …`,
   `hb1 : bd1 + 2^(n/2) ≤ bd2 + 2^(n−n/2)`, `hb2 : bd2 ≤ BD2 n + 1`,
   `hw1 : 1 ≤ w`, the canon-shaped haddr envelope, `hS`, and
   `hpair : ∀ q < 2^(n/2), q' < 2^(n−n/2), f (bd1+q) + f (bd2+q') < 2^w`
   (no-wrap envelope — REQUIRED: the 245/246 blt decisions compare
   stored w-bit sums; without it the walk is undecidable). Composition
   derivation: A[i] ≤ t0+1 (clamp), B[j] ≤ Σa, t0 ≤ maxValue, so
   A+B ≤ (maxValue+1) + Σa ≤ 2Σa < 2^w via `two_sum_lt_pow_wordLength`
   (n ≥ 2, maxValue ≥ 1).
3. GAP for the composer: `canon_exec`'s conclusion does not pin
   `f' 19 = bd2` (nor 12/13/17/22) — canon's Pres region `ARegC` covers
   ≤ 22 so those flow through the loop untouched (canon writes only
   registers {14,15,16,20,21,22}) but are not STATED. One-line additive
   strengthening of `canonLoop_exec`'s conclusion (pin `f' 12/13/17/19`
   to `f0`'s values) unblocks the 231-entry application. Not done here
   (M4 is another wave's landed file; change is additive and safe).

## M6 — Submission/Budget.lean (merged from v2-budget at `1b94b13`, extended)

- `budget_compose2 (hn : 4 ≤ n)`: the four landed phase budgets
  (phaseA `12+44(2^(n/2)−1)+24h`, phaseA2 `17+44(2^(n−h)−1)+24m`,
  canon `7·2^(n/2)+9`, scanB `30·2^(n/2)+9`) ≤ `176 * 2^(n/2) + 64 * n`.
  Design C=256/D=12 was exceeded on the LINEAR term (24n of phase
  linear work alone) — re-derived C=176, D=64 (D=64 also leaves
  prologue headroom: 6n+110 fits at n ≥ 4 alongside these four).
- `budget_final (hn : 4 ≤ n)`: `(176 * 2^(n/2) + 64 * n)^2 ≤ 61696 * 2^n`
  via generic `budget_sq`. **K = 61696** (= 176² + 2·176·64 + 2·64²).
  axioms [propext, Quot.sound].

## Gotchas hit (all resolved, in-tree)

- `exec_accept_step`/`exec_reject_step` conclude `some true/false` —
  a verdict-terminal phase CANNOT be stated pc→pc; the walk conclusion
  must be the disjunction over verdict values.
- up_ne peel chains must count DOUBLED layers (244 and 245 both write
  rVJ=16; setup writes 20 and 22 twice) — one `up_ne` per layer, and
  `rw` needs `hS5def`-style unfolds before peeling into a local-def
  state (obtain-⟨S5,hS5def⟩ pattern used throughout).
- `omega` cannot see inside atom arguments: `f (bd2+jp−1) =
  f (bd2+(jp−1))` needs an explicit congruence rewrite (`show … from by
  omega`) before omega; same for `BD2 n` — keep `hBD : BD2 n = … := rfl`
  in context.
- `Nat.pow_le_pow_right (by omega) (by omega)` on a meta-typed second
  argument mis-elaborates (picks up an unrelated `≤` hypothesis); give
  the exponent fact as a NAMED have (`hmh`) — Race.lean's pattern.
