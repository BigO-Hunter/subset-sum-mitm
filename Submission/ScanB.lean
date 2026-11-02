import Submission.Canon
set_option autoImplicit true
set_option maxHeartbeats 12000000

/-!
# ScanB: v2 two-pointer sweep (M5)

`scanB` (`Program.lean`, pcs 231..252) sweeps the clamped first-half array
`A = arr[bd1 .. bd1+2^(n/2))` with an ascending index `i` (rI = 12) and the
second-half array `B = arr[bd2 .. bd2+2^(n-n/2))` with a descending
one-past-the-end pointer `rJ` (13): it tests `A[i] + B[j]` against `t₀`
(accept at pc 247) and shrinks one pointer per iteration, rejecting on
exhaustion (pcs 239 / 252).  The loop performs **no stores**, so the sweep
sees the entry memory throughout and no `Pres` bookkeeping is needed; the
verdict wiring to the clamped array is pointwise `canon_pair_iff`
(Canon.lean) at the composition layer.

The one honest subtlety: the machine adds `w`-bit words, so the branch
decisions at pcs 245/246 compare *stored* values.  The hypotheses include
a pairwise no-wrap envelope `f (bd1+q) + f (bd2+q') < 2^w` (in the real
composition: `A[i] ≤ t₀+1` from canon, `B[j] ≤ Σa` from the spec, and
`2·Σa < 2^w` from `two_sum_lt_pow_wordLength`), which makes every branch
decidable at the Nat level.

Budget, re-derived from the landed program text (gap-map constants were
sketches): 7 setup steps; each loop iteration costs 9 (j-path) or 10
(i-path) steps; the accept exit costs 9, the i-exhaustion reject 11, the
j-exhaustion reject 2.  With measure `(2^(n/2) − i) + jp` (jp = rJ − bd2,
the B entries not yet discarded) the TRUE loop budget is
`10 * measure + 2`, giving the phase budget
`10 * (2^(n/2) + 2^(n-n/2)) + 9` ≤ `30 * 2^(n/2) + 9`.

§1 `scanLoop_exec` — one fuel-driven walk of the loop `238 → 238`.
§2 `scanB_exec` — the phase walk `231 → verdict` with the TRUE budget.
§3 `scanB_budget` — the same with `2^(n-n/2) ≤ 2·2^(n/2)` folded.
-/

namespace SubsetSum.MITM

open BigOSpeedrun.SubsetSum SubsetSum.MITM.Spec

/-! ## §0. State normalization helpers -/

/-- The loop body's six register writes (`20, 15, 21, 16, 16`, then the
path cell `c ∈ {12, 13}`) never touch memory cells above the register
file. -/
private theorem body6_ne {f : Nat → Nat} (v20 v15 v21 v16a v16b c vc q : Nat)
    (hq : 22 < q) (hqc : q ≠ c) :
    (up (up (up (up (up (up f 20 v20) 15 v15) 21 v21) 16 v16a) 16 v16b)
      c vc) q = f q := by
  rw [up_ne hqc, up_ne (show q ≠ 16 by omega),
    up_ne (show q ≠ 16 by omega), up_ne (show q ≠ 21 by omega),
    up_ne (show q ≠ 15 by omega), up_ne (show q ≠ 20 by omega)]

/-- scanB's setup writes registers `12, 13, 20, 20, 17, 22, 22` only. -/
private theorem setup7_ne (f : Nat → Nat) (v12 v13 v20a v20b v17 v22a v22b q : Nat)
    (hq : 22 < q) :
    (up (up (up (up (up (up (up f 12 v12) 13 v13) 20 v20a) 20 v20b)
      17 v17) 22 v22a) 22 v22b) q = f q := by
  rw [up_ne (show q ≠ 22 by omega), up_ne (show q ≠ 22 by omega),
    up_ne (show q ≠ 17 by omega), up_ne (show q ≠ 20 by omega),
    up_ne (show q ≠ 20 by omega), up_ne (show q ≠ 13 by omega),
    up_ne (show q ≠ 12 by omega)]

/-! ## §0b. The no-wrap envelope (M7b) -/

/-- **No-wrap envelope for the scan sweep.**  A clamped first-half entry
(`≤ t₀ + 1`, canon's clamp) plus a second-half entry (`≤ n·maxValue`,
every subset sum of at most `n` positive inputs) is below `2^w`:
`t₀ ≤ maxValue < 2^bits` and `w = 4(n+bits) + ⌈log₂(n+2)⁴⌉ + 1 ≥
bits + log₂n + 2` give `(t₀+1) + n·maxValue + 1 < 2^(bits+log₂n+2) ≤ 2^w`.
Minimal context by design (no memory, no program, no arrays — the
omega-bogus-counterexample cure): only `x`, `n ≥ 2` and three value
bounds.  Note the honest scope: `t₀` may exceed `Σa`, so the sharper
`2·Σa < 2^w` route of `two_sum_lt_pow_wordLength` does NOT apply; the
`maxValue`-roof does. -/
theorem pair_sum_lt_two_pow {n : Nat} (x : Instance n) (hn : 2 ≤ n) (w : Nat)
    (hw : wordLength n x.bits ≤ w)
    (vA vB t0 : Nat) (hvA : vA ≤ t0 + 1) (hvB : vB ≤ n * x.maxValue)
    (ht0 : t0 ≤ x.maxValue) :
    vA + vB < 2 ^ w := by
  have hpos : 0 < n := by omega
  have hmax : x.maxValue < 2 ^ x.bits := maxValue_lt_pow x hpos
  have hwdef : wordLength n x.bits
      = 4 * (n + x.bits) + Nat.log2 ((n + 2) ^ 4 - 1) + 1 := rfl
  have hlogn : Nat.log2 n ≤ n := Nat.log2_le_self n
  have hexp : x.bits + Nat.log2 n + 2 ≤ w := by omega
  have hnl : n + 1 ≤ 2 ^ (Nat.log2 n + 1) := by
    have h := log2_lt hpos
    omega
  have hpow2 : 2 ≤ 2 ^ (Nat.log2 n + 1) := by
    have h1 : 2 ^ 1 ≤ 2 ^ (Nat.log2 n + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    rwa [Nat.pow_one] at h1
  -- bridge the two product atoms (omega atomizes (n+1)·m vs n·m)
  have hsplit : (n + 1) * x.maxValue = n * x.maxValue + x.maxValue := by
    rw [Nat.add_mul, Nat.one_mul]
  have p1 : vA + vB ≤ (n + 1) * x.maxValue + 1 := by omega
  have p2 : (n + 1) * x.maxValue + 1
      < 2 ^ (Nat.log2 n + 1) * 2 ^ x.bits := by
    have e1 : (n + 1) * x.maxValue ≤ 2 ^ (Nat.log2 n + 1) * x.maxValue :=
      Nat.mul_le_mul_right x.maxValue hnl
    have hmax1 : x.maxValue + 1 ≤ 2 ^ x.bits := by omega
    have e4 : 2 ^ (Nat.log2 n + 1) * x.maxValue + 2 ^ (Nat.log2 n + 1)
        ≤ 2 ^ (Nat.log2 n + 1) * 2 ^ x.bits := by
      have h := Nat.mul_le_mul_left (2 ^ (Nat.log2 n + 1)) hmax1
      rw [Nat.mul_add, Nat.mul_one] at h
      exact h
    -- the gap: maxValue+1 ≤ 2^bits shaves 2^(log2 n+1) ≥ 2 off the roof
    omega
  have p3 : vA + vB < 2 ^ (Nat.log2 n + 1) * 2 ^ x.bits := by omega
  -- the fold: named-have exponents (Nat.pow_le_pow_right mis-elaborates
  -- on a meta-typed second argument)
  have q2 : 2 ^ (Nat.log2 n + 1) * 2 ^ x.bits ≤ 2 ^ w := by
    rw [← Nat.pow_add]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  exact Nat.lt_of_lt_of_le p3 q2

/-! ## §1. The loop (pcs 238 → 238; ≤ 10 steps per iteration, ≤ 2 to exit) -/

/-- Fuel-driven walk of scanB's loop: entered at `LSB` (pc 238) with `i`
elements consumed from `A` and `jp` entries of `B` not yet discarded
(`rJ = bd2 + jp`), exits at pc 239 (jp = 0), pc 247 (accept, with the
witness sum) or pc 252 (i exhausted).  TRUE budget `10 * measure + 2`
where the measure is `(2^(n/2) − i) + jp`. -/
theorem scanLoop_exec {w n : Nat} (ρ : Nat → BitVec w)
    (bd1 bd2 t0 : Nat) :
    ∀ (F i jp : Nat) (f : Nat → Nat) (S r : Nat),
    22 < bd1 → 22 < bd2 →
    bd1 + 2 ^ (n / 2) ≤ bd2 + 2 ^ (n - n / 2) →
    f 1 = 1 → f 2 = 0 → f 6 = bd1 → f 12 = i → f 13 = bd2 + jp →
    f 17 = t0 → f 19 = bd2 → f 22 = 2 ^ (n / 2) →
    i < 2 ^ (n / 2) → jp ≤ 2 ^ (n - n / 2) →
    (∀ q, f q < 2 ^ w) →
    (∀ c, c ≤ bd2 + 2 ^ (n - n / 2) → c < 2 ^ w) →
    (∀ q, q < 2 ^ (n / 2) → ∀ q', q' < 2 ^ (n - n / 2) →
      f (bd1 + q) + f (bd2 + q') < 2 ^ w) →
    (2 ^ (n / 2) - i) + jp ≤ F →
    10 * ((2 ^ (n / 2) - i) + jp) + 2 ≤ S →
    ∃ c, c ≤ 10 * ((2 ^ (n / 2) - i) + jp) + 2 ∧
      (exec prog2 ρ S 238 r (memOf w f) = some false
        ∨ exec prog2 ρ S 238 r (memOf w f) = some true
          ∧ ∃ i' jp', i' < 2 ^ (n / 2) ∧ 1 ≤ jp' ∧ jp' ≤ 2 ^ (n - n / 2) ∧
            f (bd1 + i') + f (bd2 + (jp' - 1)) = t0) := by
  intro F
  induction F with
  | zero =>
    intro i jp f S r hbd1 hbd2 hb1 h1 h2 h6 h12 h13 h17 h19 h22 hilt hjp
      hfit haddr hpair hfuel hS
    -- measure 0 forces jp = 0 ∧ i = 2^(n/2), contradicting i < 2^(n/2)
    exfalso; omega
  | succ F ih =>
    intro i jp f S r hbd1 hbd2 hb1 h1 h2 h6 h12 h13 h17 h19 h22 hilt hjp
      hfit haddr hpair hfuel hS
    have haA : 22 < bd1 + i := by omega
    rcases Nat.eq_zero_or_pos jp with h0 | hjp1
    · -- j exhausted: 238 falls through, 239 rejects — 2 steps
      rw [h0] at h13
      refine ⟨2, by omega, Or.inl ?_⟩
      rw [exec_blt_ge_step (S := S) (by omega)
        (show prog2.getD 238 Instr.reject = Instr.blt 19 13 240 by rfl) hfit
        (by rw [h19, h13]; omega),
        exec_reject_step (S := S - 1) (by omega)
        (show prog2.getD 239 Instr.reject = Instr.reject by rfl)]
    · -- one iteration: 238 | 240 | 241 | 242 | 243 | 244 — 6 steps to pc 245
      -- the post-body register state (loads only read; nothing stores)
      obtain ⟨S5, hS5def⟩ : ∃ g : Nat → Nat,
          g = (up (up (up (up (up f 20 (bd1 + i)) 15 (f (bd1 + i)))
            21 (bd2 + jp - 1)) 16 (f (bd2 + jp - 1)))
            16 (f (bd1 + i) + f (bd2 + (jp - 1)))) := ⟨_, rfl⟩
      have fitS1 : ∀ q, (up f 20 (bd1 + i)) q < 2 ^ w :=
        up_fit hfit (haddr (bd1 + i) (by omega))
      have fitS2 : ∀ q, (up (up f 20 (bd1 + i)) 15 (f (bd1 + i))) q < 2 ^ w :=
        up_fit fitS1 (hfit (bd1 + i))
      have fitS3 : ∀ q,
          (up (up (up f 20 (bd1 + i)) 15 (f (bd1 + i))) 21 (bd2 + jp - 1)) q
            < 2 ^ w :=
        up_fit fitS2 (haddr (bd2 + jp - 1) (by omega))
      have fitS4 : ∀ q,
          (up (up (up (up f 20 (bd1 + i)) 15 (f (bd1 + i))) 21 (bd2 + jp - 1))
            16 (f (bd2 + jp - 1))) q < 2 ^ w :=
        up_fit fitS3 (hfit (bd2 + jp - 1))
      have hs : f (bd1 + i) + f (bd2 + (jp - 1)) < 2 ^ w :=
        hpair i hilt (jp - 1) (by omega)
      have fitS5 : ∀ q, S5 q < 2 ^ w := by
        intro q; rw [hS5def]
        exact up_fit (c := 16) fitS4 hs q
      have hprefix : exec prog2 ρ S 238 r (memOf w f)
          = exec prog2 ρ (S - 6) 245 r (memOf w S5) := by
        rw [exec_blt_lt_step (S := S) (by omega)
            (show prog2.getD 238 Instr.reject = Instr.blt 19 13 240 by rfl)
            hfit (by rw [h19, h13]; omega),
          exec_add_step (S := S - 1) (by omega)
            (show prog2.getD 240 Instr.reject = Instr.add 20 6 12 by rfl),
          show (up f 20 (f 6 + f 12)) = up f 20 (bd1 + i) from by rw [h6, h12],
          exec_load_step (S := S - 1 - 1) (by omega)
            (show prog2.getD 241 Instr.reject = Instr.load 15 20 by rfl) fitS1,
          up_eq, up_ne (show (bd1:Nat) + i ≠ 20 by omega),
          exec_sub_step (S := S - 1 - 1 - 1) (by omega)
            (show prog2.getD 242 Instr.reject = Instr.sub 21 13 1 by rfl) fitS2
            (by rw [up_ne (show (1:Nat) ≠ 15 by omega),
                    up_ne (show (1:Nat) ≠ 20 by omega), h1,
                    up_ne (show (13:Nat) ≠ 15 by omega),
                    up_ne (show (13:Nat) ≠ 20 by omega), h13]; omega),
          show (up (up f 20 (bd1 + i)) 15 (f (bd1 + i))) 13
                - (up (up f 20 (bd1 + i)) 15 (f (bd1 + i))) 1
              = bd2 + jp - 1 from by
            rw [up_ne (show (13:Nat) ≠ 15 by omega),
                up_ne (show (13:Nat) ≠ 20 by omega), h13,
                up_ne (show (1:Nat) ≠ 15 by omega),
                up_ne (show (1:Nat) ≠ 20 by omega), h1],
          exec_load_step (S := S - 1 - 1 - 1 - 1) (by omega)
            (show prog2.getD 243 Instr.reject = Instr.load 16 21 by rfl) fitS3,
          up_eq,
          up_ne (show (bd2:Nat) + jp - 1 ≠ 21 by omega),
          up_ne (show (bd2:Nat) + jp - 1 ≠ 15 by omega),
          up_ne (show (bd2:Nat) + jp - 1 ≠ 20 by omega),
          exec_add_step (S := S - 1 - 1 - 1 - 1 - 1) (by omega)
            (show prog2.getD 244 Instr.reject = Instr.add 16 15 16 by rfl),
          show (up (up (up (up f 20 (bd1 + i)) 15 (f (bd1 + i)))
                21 (bd2 + jp - 1)) 16 (f (bd2 + jp - 1))) 15
              + (up (up (up (up f 20 (bd1 + i)) 15 (f (bd1 + i)))
                21 (bd2 + jp - 1)) 16 (f (bd2 + jp - 1))) 16
              = f (bd1 + i) + f (bd2 + (jp - 1)) from by
            rw [up_ne (show (15:Nat) ≠ 16 by omega),
                up_ne (show (15:Nat) ≠ 21 by omega), up_eq, up_eq,
                show (bd2 + jp - 1 : Nat) = bd2 + (jp - 1) from by omega],
          hS5def,
          show (S - 1 - 1 - 1 - 1 - 1 - 1 : Nat) = S - 6 from by omega]
      -- the three-way branch at pcs 245/246 on s = A[i] + B[j-1] vs t₀
      have h17S5 : S5 17 = t0 := by
        rw [hS5def, up_ne (show (17:Nat) ≠ 16 by omega),
            up_ne (show (17:Nat) ≠ 16 by omega),
            up_ne (show (17:Nat) ≠ 21 by omega),
            up_ne (show (17:Nat) ≠ 15 by omega),
            up_ne (show (17:Nat) ≠ 20 by omega), h17]
      have h16S5 : S5 16 = f (bd1 + i) + f (bd2 + (jp - 1)) := by
        rw [hS5def, up_eq]
      rcases Nat.lt_trichotomy t0 (f (bd1 + i) + f (bd2 + (jp - 1))) with
        hgt | heq | hlt
      · -- s > t₀: shrink j (245 taken, 248, 249 back to 238 — 9 steps)
        obtain ⟨JB, hJBdef⟩ : ∃ g : Nat → Nat, g = up S5 13 (bd2 + jp - 1) :=
          ⟨_, rfl⟩
        have fitJB : ∀ q, JB q < 2 ^ w := by
          intro q; rw [hJBdef]
          by_cases hq13 : q = 13
          · subst hq13; rw [up_eq]; exact haddr (bd2 + jp - 1) (by omega)
          · rw [up_ne hq13]; exact fitS5 q
        have hpJB : ∀ q, q < 2 ^ (n / 2) → ∀ q', q' < 2 ^ (n - n / 2) →
            JB (bd1 + q) + JB (bd2 + q') < 2 ^ w := by
          intro q hq q' hq'
          rw [hJBdef, hS5def,
            body6_ne (bd1 + i) (f (bd1 + i)) (bd2 + jp - 1)
              (f (bd2 + jp - 1)) (f (bd1 + i) + f (bd2 + (jp - 1))) 13
              (bd2 + jp - 1) (bd1 + q) (by omega) (by omega),
            body6_ne (bd1 + i) (f (bd1 + i)) (bd2 + jp - 1)
              (f (bd2 + jp - 1)) (f (bd1 + i) + f (bd2 + (jp - 1))) 13
              (bd2 + jp - 1) (bd2 + q') (by omega) (by omega)]
          exact hpair q hq q' hq'
        have hbodyJ : exec prog2 ρ S 238 r (memOf w f)
            = exec prog2 ρ (S - 9) 238 r (memOf w JB) := by
          rw [hprefix,
            exec_blt_lt_step (S := S - 6) (by omega)
              (show prog2.getD 245 Instr.reject = Instr.blt 17 16 248 by rfl)
              fitS5 (by rw [h17S5, h16S5]; omega),
            exec_sub_step (S := S - 6 - 1) (by omega)
              (show prog2.getD 248 Instr.reject = Instr.sub 13 13 1 by rfl)
              fitS5
              (by rw [hS5def,
                      up_ne (show (1:Nat) ≠ 16 by omega),
                      up_ne (show (1:Nat) ≠ 16 by omega),
                      up_ne (show (1:Nat) ≠ 21 by omega),
                      up_ne (show (1:Nat) ≠ 15 by omega),
                      up_ne (show (1:Nat) ≠ 20 by omega), h1,
                      up_ne (show (13:Nat) ≠ 16 by omega),
                      up_ne (show (13:Nat) ≠ 16 by omega),
                      up_ne (show (13:Nat) ≠ 21 by omega),
                      up_ne (show (13:Nat) ≠ 15 by omega),
                      up_ne (show (13:Nat) ≠ 20 by omega), h13]; omega),
            show S5 13 - S5 1 = bd2 + jp - 1 from by
              rw [hS5def,
                  up_ne (show (13:Nat) ≠ 16 by omega),
                  up_ne (show (13:Nat) ≠ 16 by omega),
                  up_ne (show (13:Nat) ≠ 21 by omega),
                  up_ne (show (13:Nat) ≠ 15 by omega),
                  up_ne (show (13:Nat) ≠ 20 by omega), h13,
                  up_ne (show (1:Nat) ≠ 16 by omega),
                  up_ne (show (1:Nat) ≠ 16 by omega),
                  up_ne (show (1:Nat) ≠ 21 by omega),
                  up_ne (show (1:Nat) ≠ 15 by omega),
                  up_ne (show (1:Nat) ≠ 20 by omega), h1],
            ← hJBdef,
            exec_blt_lt_step (S := S - 6 - 1 - 1) (by omega)
              (show prog2.getD 249 Instr.reject = Instr.blt 2 1 238 by rfl)
              fitJB (by rw [hJBdef,
                              up_ne (show (2:Nat) ≠ 13 by omega),
                              hS5def,
                              up_ne (show (2:Nat) ≠ 16 by omega),
                              up_ne (show (2:Nat) ≠ 16 by omega),
                              up_ne (show (2:Nat) ≠ 21 by omega),
                              up_ne (show (2:Nat) ≠ 15 by omega),
                              up_ne (show (2:Nat) ≠ 20 by omega), h2,
                              up_ne (show (1:Nat) ≠ 13 by omega),
                              up_ne (show (1:Nat) ≠ 16 by omega),
                              up_ne (show (1:Nat) ≠ 16 by omega),
                              up_ne (show (1:Nat) ≠ 21 by omega),
                              up_ne (show (1:Nat) ≠ 15 by omega),
                              up_ne (show (1:Nat) ≠ 20 by omega), h1]; omega),
            show (S - 6 - 1 - 1 - 1 : Nat) = S - 9 from by omega]
        -- recurse: the measure drops by exactly 1
        obtain ⟨c', hc', hex'⟩ :=
          ih i (jp - 1) JB (S - 9) r hbd1 hbd2 hb1
            (by rw [hJBdef, up_ne (show (1:Nat) ≠ 13 by omega),
                    hS5def,
                    up_ne (show (1:Nat) ≠ 16 by omega),
                    up_ne (show (1:Nat) ≠ 16 by omega),
                    up_ne (show (1:Nat) ≠ 21 by omega),
                    up_ne (show (1:Nat) ≠ 15 by omega),
                    up_ne (show (1:Nat) ≠ 20 by omega), h1])
            (by rw [hJBdef, up_ne (show (2:Nat) ≠ 13 by omega),
                    hS5def,
                    up_ne (show (2:Nat) ≠ 16 by omega),
                    up_ne (show (2:Nat) ≠ 16 by omega),
                    up_ne (show (2:Nat) ≠ 21 by omega),
                    up_ne (show (2:Nat) ≠ 15 by omega),
                    up_ne (show (2:Nat) ≠ 20 by omega), h2])
            (by rw [hJBdef, up_ne (show (6:Nat) ≠ 13 by omega),
                    hS5def,
                    up_ne (show (6:Nat) ≠ 16 by omega),
                    up_ne (show (6:Nat) ≠ 16 by omega),
                    up_ne (show (6:Nat) ≠ 21 by omega),
                    up_ne (show (6:Nat) ≠ 15 by omega),
                    up_ne (show (6:Nat) ≠ 20 by omega), h6])
            (by rw [hJBdef, up_ne (show (12:Nat) ≠ 13 by omega),
                    hS5def,
                    up_ne (show (12:Nat) ≠ 16 by omega),
                    up_ne (show (12:Nat) ≠ 16 by omega),
                    up_ne (show (12:Nat) ≠ 21 by omega),
                    up_ne (show (12:Nat) ≠ 15 by omega),
                    up_ne (show (12:Nat) ≠ 20 by omega), h12])
            (by rw [hJBdef, up_eq]; omega)
            (by rw [hJBdef, up_ne (show (17:Nat) ≠ 13 by omega),
                    hS5def,
                    up_ne (show (17:Nat) ≠ 16 by omega),
                    up_ne (show (17:Nat) ≠ 16 by omega),
                    up_ne (show (17:Nat) ≠ 21 by omega),
                    up_ne (show (17:Nat) ≠ 15 by omega),
                    up_ne (show (17:Nat) ≠ 20 by omega), h17])
            (by rw [hJBdef, up_ne (show (19:Nat) ≠ 13 by omega),
                    hS5def,
                    up_ne (show (19:Nat) ≠ 16 by omega),
                    up_ne (show (19:Nat) ≠ 16 by omega),
                    up_ne (show (19:Nat) ≠ 21 by omega),
                    up_ne (show (19:Nat) ≠ 15 by omega),
                    up_ne (show (19:Nat) ≠ 20 by omega), h19])
            (by rw [hJBdef, up_ne (show (22:Nat) ≠ 13 by omega),
                    hS5def,
                    up_ne (show (22:Nat) ≠ 16 by omega),
                    up_ne (show (22:Nat) ≠ 16 by omega),
                    up_ne (show (22:Nat) ≠ 21 by omega),
                    up_ne (show (22:Nat) ≠ 15 by omega),
                    up_ne (show (22:Nat) ≠ 20 by omega), h22])
            hilt (by omega) fitJB haddr hpJB (by omega) (by omega)
        refine ⟨9 + c', by omega, ?_⟩
        rcases hex' with hex' | ⟨hex', i', jp', hi', hj1', hjN', hwit'⟩
        · exact Or.inl (by rw [hbodyJ, hex'])
        · refine Or.inr ⟨by rw [hbodyJ, hex'], i', jp', hi', hj1', hjN', ?_⟩
          rw [hJBdef, hS5def,
            body6_ne (bd1 + i) (f (bd1 + i)) (bd2 + jp - 1)
              (f (bd2 + jp - 1)) (f (bd1 + i) + f (bd2 + (jp - 1))) 13
              (bd2 + jp - 1) (bd1 + i') (by omega) (by omega),
            body6_ne (bd1 + i) (f (bd1 + i)) (bd2 + jp - 1)
              (f (bd2 + jp - 1)) (f (bd1 + i) + f (bd2 + (jp - 1))) 13
              (bd2 + jp - 1) (bd2 + (jp' - 1)) (by omega) (by omega)] at hwit'
          exact hwit'
      · -- s = t₀: 245 falls through, 246 falls through, 247 accepts — 9 steps
        refine ⟨9, by omega, Or.inr ⟨?_, i, jp, hilt, hjp1, hjp, ?_⟩⟩
        · rw [hprefix,
          exec_blt_ge_step (S := S - 6) (by omega)
            (show prog2.getD 245 Instr.reject = Instr.blt 17 16 248 by rfl)
            fitS5 (by rw [h17S5, h16S5]; omega),
          exec_blt_ge_step (S := S - 6 - 1) (by omega)
            (show prog2.getD 246 Instr.reject = Instr.blt 16 17 250 by rfl)
            fitS5 (by rw [h17S5, h16S5]; omega),
          exec_accept_step (S := S - 6 - 1 - 1) (by omega)
            (show prog2.getD 247 Instr.reject = Instr.accept by rfl)]
        · omega
      · -- s < t₀: grow i (245 falls, 246 taken, 250, 251 — 10 steps)
        obtain ⟨IA, hIAdef⟩ : ∃ g : Nat → Nat, g = up S5 12 (i + 1) :=
          ⟨_, rfl⟩
        have fitIA : ∀ q, IA q < 2 ^ w := by
          intro q; rw [hIAdef]
          by_cases hq12 : q = 12
          · subst hq12; rw [up_eq]; exact haddr (i + 1) (by omega)
          · rw [up_ne hq12]; exact fitS5 q
        have hpIA : ∀ q, q < 2 ^ (n / 2) → ∀ q', q' < 2 ^ (n - n / 2) →
            IA (bd1 + q) + IA (bd2 + q') < 2 ^ w := by
          intro q hq q' hq'
          rw [hIAdef, hS5def,
            body6_ne (bd1 + i) (f (bd1 + i)) (bd2 + jp - 1)
              (f (bd2 + jp - 1)) (f (bd1 + i) + f (bd2 + (jp - 1))) 12
              (i + 1) (bd1 + q) (by omega) (by omega),
            body6_ne (bd1 + i) (f (bd1 + i)) (bd2 + jp - 1)
              (f (bd2 + jp - 1)) (f (bd1 + i) + f (bd2 + (jp - 1))) 12
              (i + 1) (bd2 + q') (by omega) (by omega)]
          exact hpair q hq q' hq'
        rcases Nat.lt_or_ge (i + 1) (2 ^ (n / 2)) with hilt' | hiex
        · -- i+1 < 2^h: back to 238 (10 steps)
          have hbodyI : exec prog2 ρ S 238 r (memOf w f)
              = exec prog2 ρ (S - 10) 238 r (memOf w IA) := by
            rw [hprefix,
              exec_blt_ge_step (S := S - 6) (by omega)
                (show prog2.getD 245 Instr.reject = Instr.blt 17 16 248 by rfl)
                fitS5 (by rw [h17S5, h16S5]; omega),
              exec_blt_lt_step (S := S - 6 - 1) (by omega)
                (show prog2.getD 246 Instr.reject = Instr.blt 16 17 250 by rfl)
                fitS5 (by rw [h16S5, h17S5]; omega),
              exec_add_step (S := S - 6 - 1 - 1) (by omega)
                (show prog2.getD 250 Instr.reject = Instr.add 12 12 1 by rfl),
              show S5 12 + S5 1 = i + 1 from by
                rw [hS5def,
                    up_ne (show (12:Nat) ≠ 16 by omega),
                    up_ne (show (12:Nat) ≠ 16 by omega),
                    up_ne (show (12:Nat) ≠ 21 by omega),
                    up_ne (show (12:Nat) ≠ 15 by omega),
                    up_ne (show (12:Nat) ≠ 20 by omega), h12,
                    up_ne (show (1:Nat) ≠ 16 by omega),
                    up_ne (show (1:Nat) ≠ 16 by omega),
                    up_ne (show (1:Nat) ≠ 21 by omega),
                    up_ne (show (1:Nat) ≠ 15 by omega),
                    up_ne (show (1:Nat) ≠ 20 by omega), h1],
              ← hIAdef,
              exec_blt_lt_step (S := S - 6 - 1 - 1 - 1) (by omega)
                (show prog2.getD 251 Instr.reject = Instr.blt 12 22 238 by rfl)
                fitIA (by rw [hIAdef,
                                up_ne (show (22:Nat) ≠ 12 by omega), up_eq,
                                hS5def, up_ne (show (22:Nat) ≠ 16 by omega),
                                up_ne (show (22:Nat) ≠ 16 by omega),
                                up_ne (show (22:Nat) ≠ 21 by omega),
                                up_ne (show (22:Nat) ≠ 15 by omega),
                                up_ne (show (22:Nat) ≠ 20 by omega),
                                h22]; omega),
              show (S - 6 - 1 - 1 - 1 - 1 : Nat) = S - 10 from by omega]
          obtain ⟨c', hc', hex'⟩ :=
            ih (i + 1) jp IA (S - 10) r hbd1 hbd2 hb1
              (by rw [hIAdef, up_ne (show (1:Nat) ≠ 12 by omega),
                      hS5def,
                      up_ne (show (1:Nat) ≠ 16 by omega),
                      up_ne (show (1:Nat) ≠ 16 by omega),
                      up_ne (show (1:Nat) ≠ 21 by omega),
                      up_ne (show (1:Nat) ≠ 15 by omega),
                      up_ne (show (1:Nat) ≠ 20 by omega), h1])
              (by rw [hIAdef, up_ne (show (2:Nat) ≠ 12 by omega),
                      hS5def,
                      up_ne (show (2:Nat) ≠ 16 by omega),
                      up_ne (show (2:Nat) ≠ 16 by omega),
                      up_ne (show (2:Nat) ≠ 21 by omega),
                      up_ne (show (2:Nat) ≠ 15 by omega),
                      up_ne (show (2:Nat) ≠ 20 by omega), h2])
              (by rw [hIAdef, up_ne (show (6:Nat) ≠ 12 by omega),
                      hS5def,
                      up_ne (show (6:Nat) ≠ 16 by omega),
                      up_ne (show (6:Nat) ≠ 16 by omega),
                      up_ne (show (6:Nat) ≠ 21 by omega),
                      up_ne (show (6:Nat) ≠ 15 by omega),
                      up_ne (show (6:Nat) ≠ 20 by omega), h6])
              (by rw [hIAdef, up_eq])
              (by rw [hIAdef, up_ne (show (13:Nat) ≠ 12 by omega),
                      hS5def,
                      up_ne (show (13:Nat) ≠ 16 by omega),
                      up_ne (show (13:Nat) ≠ 16 by omega),
                      up_ne (show (13:Nat) ≠ 21 by omega),
                      up_ne (show (13:Nat) ≠ 15 by omega),
                      up_ne (show (13:Nat) ≠ 20 by omega), h13])
              (by rw [hIAdef, up_ne (show (17:Nat) ≠ 12 by omega),
                      hS5def,
                      up_ne (show (17:Nat) ≠ 16 by omega),
                      up_ne (show (17:Nat) ≠ 16 by omega),
                      up_ne (show (17:Nat) ≠ 21 by omega),
                      up_ne (show (17:Nat) ≠ 15 by omega),
                      up_ne (show (17:Nat) ≠ 20 by omega), h17])
              (by rw [hIAdef, up_ne (show (19:Nat) ≠ 12 by omega),
                      hS5def,
                      up_ne (show (19:Nat) ≠ 16 by omega),
                      up_ne (show (19:Nat) ≠ 16 by omega),
                      up_ne (show (19:Nat) ≠ 21 by omega),
                      up_ne (show (19:Nat) ≠ 15 by omega),
                      up_ne (show (19:Nat) ≠ 20 by omega), h19])
              (by rw [hIAdef, up_ne (show (22:Nat) ≠ 12 by omega),
                      hS5def,
                      up_ne (show (22:Nat) ≠ 16 by omega),
                      up_ne (show (22:Nat) ≠ 16 by omega),
                      up_ne (show (22:Nat) ≠ 21 by omega),
                      up_ne (show (22:Nat) ≠ 15 by omega),
                      up_ne (show (22:Nat) ≠ 20 by omega), h22])
              hilt' hjp fitIA haddr hpIA (by omega) (by omega)
          refine ⟨10 + c', by omega, ?_⟩
          rcases hex' with hex' | ⟨hex', i', jp', hi', hj1', hjN', hwit'⟩
          · exact Or.inl (by rw [hbodyI, hex'])
          · refine Or.inr ⟨by rw [hbodyI, hex'], i', jp', hi', hj1', hjN', ?_⟩
            rw [hIAdef, hS5def,
              body6_ne (bd1 + i) (f (bd1 + i)) (bd2 + jp - 1)
                (f (bd2 + jp - 1)) (f (bd1 + i) + f (bd2 + (jp - 1))) 12
                (i + 1) (bd1 + i') (by omega) (by omega),
              body6_ne (bd1 + i) (f (bd1 + i)) (bd2 + jp - 1)
                (f (bd2 + jp - 1)) (f (bd1 + i) + f (bd2 + (jp - 1))) 12
                (i + 1) (bd2 + (jp' - 1)) (by omega) (by omega)] at hwit'
            exact hwit'
        · -- i exhausted: 251 falls through, 252 rejects — 11 steps
          refine ⟨11, by omega, Or.inl ?_⟩
          rw [hprefix,
            exec_blt_ge_step (S := S - 6) (by omega)
              (show prog2.getD 245 Instr.reject = Instr.blt 17 16 248 by rfl)
              fitS5 (by rw [h17S5, h16S5]; omega),
            exec_blt_lt_step (S := S - 6 - 1) (by omega)
              (show prog2.getD 246 Instr.reject = Instr.blt 16 17 250 by rfl)
              fitS5 (by rw [h16S5, h17S5]; omega),
            exec_add_step (S := S - 6 - 1 - 1) (by omega)
              (show prog2.getD 250 Instr.reject = Instr.add 12 12 1 by rfl),
            show S5 12 + S5 1 = i + 1 from by
              rw [hS5def,
                  up_ne (show (12:Nat) ≠ 16 by omega),
                  up_ne (show (12:Nat) ≠ 16 by omega),
                  up_ne (show (12:Nat) ≠ 21 by omega),
                  up_ne (show (12:Nat) ≠ 15 by omega),
                  up_ne (show (12:Nat) ≠ 20 by omega), h12,
                  up_ne (show (1:Nat) ≠ 16 by omega),
                  up_ne (show (1:Nat) ≠ 16 by omega),
                  up_ne (show (1:Nat) ≠ 21 by omega),
                  up_ne (show (1:Nat) ≠ 15 by omega),
                  up_ne (show (1:Nat) ≠ 20 by omega), h1],
            ← hIAdef,
            exec_blt_ge_step (S := S - 6 - 1 - 1 - 1) (by omega)
              (show prog2.getD 251 Instr.reject = Instr.blt 12 22 238 by rfl)
              fitIA (by rw [hIAdef,
                              up_ne (show (22:Nat) ≠ 12 by omega), up_eq,
                              hS5def, up_ne (show (22:Nat) ≠ 16 by omega),
                              up_ne (show (22:Nat) ≠ 16 by omega),
                              up_ne (show (22:Nat) ≠ 21 by omega),
                              up_ne (show (22:Nat) ≠ 15 by omega),
                              up_ne (show (22:Nat) ≠ 20 by omega),
                              h22]; omega),
            exec_reject_step (S := S - 6 - 1 - 1 - 1 - 1) (by omega)
              (show prog2.getD 252 Instr.reject = Instr.reject by rfl)]

/-! ## §2. The phase walk (231 → verdict) -/

/-- scanB's phase walk: 7 setup steps (231..237: i := 0, rJ := bd2 +
2^(n−n/2), t₀ := mem[3n+24], rT3 := 2^(n/2)), then the sweep.  TRUE phase
budget `10 * (2^(n/2) + 2^(n-n/2)) + 9`.  The accept verdict carries the
witness `(i, jp)` with `f (bd1+i) + f (bd2+(jp−1)) = t₀` — at the
composition layer `f (bd1+i)` is `clamp t₀ v` and `canon_pair_iff`
converts to the unclamped pair. -/
theorem scanB_exec {w n : Nat} (ρ : Nat → BitVec w)
    (f : Nat → Nat) (bd1 bd2 t0 : Nat) (r S : Nat)
    (hbd1 : 22 < bd1) (hbd2 : 22 < bd2)
    (hb1 : bd1 + 2 ^ (n / 2) ≤ bd2 + 2 ^ (n - n / 2))
    (hb2 : bd2 + 2 ^ (n - n / 2) ≤ BD2 n + 2 * 2 ^ (n - n / 2) + 1)
    (hw1 : 1 ≤ w)
    (hfit : ∀ q, f q < 2 ^ w)
    (h1 : f 1 = 1) (h2 : f 2 = 0) (h6 : f 6 = bd1) (h7 : f 7 = n)
    (h8 : f 8 = 2 * n + 23) (h9 : f 9 = n / 2)
    (h11 : f 11 = 2 ^ (n - n / 2)) (h19 : f 19 = bd2)
    (ht0 : f (3 * n + 24) = t0)
    (haddr : ∀ c, c ≤ BD2 n + 2 * 2 ^ (n - n / 2) + 1 → c < 2 ^ w)
    (hpair : ∀ q, q < 2 ^ (n / 2) → ∀ q', q' < 2 ^ (n - n / 2) →
      f (bd1 + q) + f (bd2 + q') < 2 ^ w)
    (hS : 10 * (2 ^ (n / 2) + 2 ^ (n - n / 2)) + 9 ≤ S) :
    ∃ c, c ≤ 10 * (2 ^ (n / 2) + 2 ^ (n - n / 2)) + 9 ∧
      (exec prog2 ρ S 231 r (memOf w f) = some false
        ∨ exec prog2 ρ S 231 r (memOf w f) = some true
          ∧ ∃ i jp, i < 2 ^ (n / 2) ∧ 1 ≤ jp ∧ jp ≤ 2 ^ (n - n / 2) ∧
            f (bd1 + i) + f (bd2 + (jp - 1)) = t0) := by
  have hpow1 : (1:Nat) ≤ 2 ^ (n / 2) := Nat.one_le_two_pow
  have hpowHalf : 2 ^ (n / 2) ≤ 2 ^ (n - n / 2) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hBD : BD2 n = 3 * n + 25 + 2 * 2 ^ (n / 2) + 2 := rfl
  have h0lt : (0:Nat) < 2 ^ w := Nat.one_le_two_pow (n := w)
  have h1lt : (1:Nat) < 2 ^ w := by
    have h : 2 ^ 1 ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hw1
    rw [Nat.pow_one] at h
    omega
  have henv : ∀ c, c ≤ bd2 + 2 ^ (n - n / 2) → c < 2 ^ w := by
    intro c hc; exact haddr c (by omega)
  -- the 7-step setup walk (pcs 231..237)
  obtain ⟨G7, hG7def⟩ : ∃ g : Nat → Nat,
      g = (up (up (up (up (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2)))
        20 (3 * n + 23)) 20 (3 * n + 24)) 17 t0) 22 1) 22 (2 ^ (n / 2))) :=
    ⟨_, rfl⟩
  have fit1 : ∀ q, (up f 12 0) q < 2 ^ w := up_fit hfit h0lt
  have fit2 : ∀ q, (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2))) q < 2 ^ w :=
    up_fit fit1 (henv (bd2 + 2 ^ (n - n / 2)) (by omega))
  have fit3 : ∀ q,
      (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2))) 20 (3 * n + 23)) q
        < 2 ^ w := up_fit fit2 (haddr (3 * n + 23) (by omega))
  have fit4 : ∀ q,
      (up (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2))) 20 (3 * n + 23))
        20 (3 * n + 24)) q < 2 ^ w := up_fit fit3 (haddr (3 * n + 24) (by omega))
  have ht0l : t0 < 2 ^ w := by rw [← ht0]; exact hfit (3 * n + 24)
  have fit5 : ∀ q,
      (up (up (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2)))
        20 (3 * n + 23)) 20 (3 * n + 24)) 17 t0) q < 2 ^ w := up_fit fit4 ht0l
  have fit6 : ∀ q,
      (up (up (up (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2)))
        20 (3 * n + 23)) 20 (3 * n + 24)) 17 t0) 22 1) q < 2 ^ w :=
    up_fit fit5 h1lt
  have fit7 : ∀ q, G7 q < 2 ^ w := by
    intro q; rw [hG7def]
    exact up_fit (c := 22) fit6 (haddr (2 ^ (n / 2)) (by omega)) q
  have hmul237 :
      (up (up (up (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2)))
        20 (3 * n + 23)) 20 (3 * n + 24)) 17 t0) 22 1) 22
        * 2 ^ (up (up (up (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2)))
        20 (3 * n + 23)) 20 (3 * n + 24)) 17 t0) 22 1) 9
      < 2 ^ w := by
    rw [up_eq, up_ne (show (9:Nat) ≠ 22 by omega),
        up_ne (show (9:Nat) ≠ 17 by omega),
        up_ne (show (9:Nat) ≠ 20 by omega),
        up_ne (show (9:Nat) ≠ 20 by omega),
        up_ne (show (9:Nat) ≠ 13 by omega),
        up_ne (show (9:Nat) ≠ 12 by omega), h9, Nat.one_mul]
    exact haddr (2 ^ (n / 2)) (by omega)
  have e231 : exec prog2 ρ S 231 r (memOf w f)
      = exec prog2 ρ (S - 1) 232 r (memOf w (up f 12 (f 12 - f 12))) :=
    exec_sub_step (S := S) (by omega)
      (show prog2.getD 231 Instr.reject = Instr.sub 12 12 12 by rfl) hfit
      (by omega)
  have n231 : up f 12 (f 12 - f 12) = (up f 12 0) := by
    rw [show f 12 - f 12 = 0 from by omega]
  have e232 : exec prog2 ρ (S - 1) 232 r (memOf w (up f 12 0))
      = exec prog2 ρ (S - 1 - 1) 233 r
          (memOf w (up (up f 12 0) 13
            ((up f 12 0) 19 + (up f 12 0) 11))) :=
    exec_add_step (S := S - 1) (by omega)
      (show prog2.getD 232 Instr.reject = Instr.add 13 19 11 by rfl)
  have n232 : (up f 12 0) 19 + (up f 12 0) 11 = bd2 + 2 ^ (n - n / 2) := by
    rw [up_ne (show (19:Nat) ≠ 12 by omega), h19,
        up_ne (show (11:Nat) ≠ 12 by omega), h11]
  have e233 : exec prog2 ρ (S - 1 - 1) 233 r
          (memOf w (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2))))
      = exec prog2 ρ (S - 1 - 1 - 1) 234 r
          (memOf w (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2))) 20
            ((up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2))) 8
              + (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2))) 7))) :=
    exec_add_step (S := S - 1 - 1) (by omega)
      (show prog2.getD 233 Instr.reject = Instr.add 20 8 7 by rfl)
  have n233 : (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2))) 8
        + (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2))) 7 = 3 * n + 23 := by
    rw [up_ne (show (8:Nat) ≠ 13 by omega),
        up_ne (show (8:Nat) ≠ 12 by omega), h8,
        up_ne (show (7:Nat) ≠ 13 by omega),
        up_ne (show (7:Nat) ≠ 12 by omega), h7]
    omega
  have e234 : exec prog2 ρ (S - 1 - 1 - 1) 234 r
          (memOf w (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2)))
            20 (3 * n + 23)))
      = exec prog2 ρ (S - 1 - 1 - 1 - 1) 235 r
          (memOf w (up (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2)))
            20 (3 * n + 23)) 20
            ((up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2))) 20 (3 * n + 23)) 20
              + (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2))) 20 (3 * n + 23))
                1))) :=
    exec_add_step (S := S - 1 - 1 - 1) (by omega)
      (show prog2.getD 234 Instr.reject = Instr.add 20 20 1 by rfl)
  have n234 : (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2))) 20 (3 * n + 23)) 20
        + (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2))) 20 (3 * n + 23)) 1
      = 3 * n + 24 := by
    rw [up_eq, up_ne (show (1:Nat) ≠ 20 by omega),
        up_ne (show (1:Nat) ≠ 13 by omega),
        up_ne (show (1:Nat) ≠ 12 by omega), h1]
  have e235 : exec prog2 ρ (S - 1 - 1 - 1 - 1) 235 r
          (memOf w (up (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2)))
            20 (3 * n + 23)) 20 (3 * n + 24)))
      = exec prog2 ρ (S - 1 - 1 - 1 - 1 - 1) 236 r
          (memOf w (up (up (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2)))
            20 (3 * n + 23)) 20 (3 * n + 24)) 17
            ((up (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2)))
              20 (3 * n + 23)) 20 (3 * n + 24))
              ((up (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2)))
                20 (3 * n + 23)) 20 (3 * n + 24)) 20)))) :=
    exec_load_step (S := S - 1 - 1 - 1 - 1) (by omega)
      (show prog2.getD 235 Instr.reject = Instr.load 17 20 by rfl) fit4
  have n235 : (up (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2)))
        20 (3 * n + 23)) 20 (3 * n + 24))
        ((up (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2))) 20 (3 * n + 23))
          20 (3 * n + 24)) 20)
      = t0 := by
    rw [up_eq,
        up_ne (show (3 * n + 24 : Nat) ≠ 20 by omega),
        up_ne (show (3 * n + 24 : Nat) ≠ 20 by omega),
        up_ne (show (3 * n + 24 : Nat) ≠ 13 by omega),
        up_ne (show (3 * n + 24 : Nat) ≠ 12 by omega), ht0]
  have e236 : exec prog2 ρ (S - 1 - 1 - 1 - 1 - 1) 236 r
          (memOf w (up (up (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2)))
            20 (3 * n + 23)) 20 (3 * n + 24)) 17 t0))
      = exec prog2 ρ (S - 1 - 1 - 1 - 1 - 1 - 1) 237 r
          (memOf w (up (up (up (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2)))
            20 (3 * n + 23)) 20 (3 * n + 24)) 17 t0) 22
            ((up (up (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2)))
              20 (3 * n + 23)) 20 (3 * n + 24)) 17 t0) 1
              + (up (up (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2)))
                20 (3 * n + 23)) 20 (3 * n + 24)) 17 t0) 2))) :=
    exec_add_step (S := S - 1 - 1 - 1 - 1 - 1) (by omega)
      (show prog2.getD 236 Instr.reject = Instr.add 22 1 2 by rfl)
  have n236 : (up (up (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2)))
        20 (3 * n + 23)) 20 (3 * n + 24)) 17 t0) 1
        + (up (up (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2)))
          20 (3 * n + 23)) 20 (3 * n + 24)) 17 t0) 2
      = 1 := by
    rw [up_ne (show (1:Nat) ≠ 17 by omega),
        up_ne (show (1:Nat) ≠ 20 by omega),
        up_ne (show (1:Nat) ≠ 20 by omega),
        up_ne (show (1:Nat) ≠ 13 by omega),
        up_ne (show (1:Nat) ≠ 12 by omega), h1,
        up_ne (show (2:Nat) ≠ 17 by omega),
        up_ne (show (2:Nat) ≠ 20 by omega),
        up_ne (show (2:Nat) ≠ 20 by omega),
        up_ne (show (2:Nat) ≠ 13 by omega),
        up_ne (show (2:Nat) ≠ 12 by omega), h2]
  have e237 : exec prog2 ρ (S - 1 - 1 - 1 - 1 - 1 - 1) 237 r
          (memOf w (up (up (up (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2)))
            20 (3 * n + 23)) 20 (3 * n + 24)) 17 t0) 22 1))
      = exec prog2 ρ (S - 7) 238 r
          (memOf w (up (up (up (up (up (up (up f 12 0)
            13 (bd2 + 2 ^ (n - n / 2))) 20 (3 * n + 23)) 20 (3 * n + 24))
            17 t0) 22 1) 22
            ((up (up (up (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2)))
              20 (3 * n + 23)) 20 (3 * n + 24)) 17 t0) 22 1) 22
              * 2 ^ (up (up (up (up (up (up f 12 0)
                13 (bd2 + 2 ^ (n - n / 2))) 20 (3 * n + 23)) 20 (3 * n + 24))
                17 t0) 22 1) 9))) :=
    exec_shl_step (S := S - 1 - 1 - 1 - 1 - 1 - 1) (by omega)
      (show prog2.getD 237 Instr.reject = Instr.shl 22 22 9 by rfl) fit6
      hmul237
  have n237 : (up (up (up (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2)))
        20 (3 * n + 23)) 20 (3 * n + 24)) 17 t0) 22 1) 22
        * 2 ^ (up (up (up (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2)))
          20 (3 * n + 23)) 20 (3 * n + 24)) 17 t0) 22 1) 9
      = 2 ^ (n / 2) := by
    rw [up_eq, up_ne (show (9:Nat) ≠ 22 by omega),
        up_ne (show (9:Nat) ≠ 17 by omega),
        up_ne (show (9:Nat) ≠ 20 by omega),
        up_ne (show (9:Nat) ≠ 20 by omega),
        up_ne (show (9:Nat) ≠ 13 by omega),
        up_ne (show (9:Nat) ≠ 12 by omega), h9, Nat.one_mul]
  have hsetup : exec prog2 ρ S 231 r (memOf w f)
      = exec prog2 ρ (S - 7) 238 r (memOf w G7) := by
    rw [e231, n231, e232, n232, e233, n233, e234, n234, e235, n235, e236,
      n236, e237, n237, hG7def]
  -- the loop, entered with i = 0, jp = 2^(n−n/2)
  obtain ⟨cL, hcL, hexL⟩ :=
    scanLoop_exec ρ bd1 bd2 t0 (2 ^ (n / 2) + 2 ^ (n - n / 2)) 0
      (2 ^ (n - n / 2)) G7 (S - 7) r hbd1 hbd2 hb1
      (by rw [hG7def, up_ne (show (1:Nat) ≠ 22 by omega),
              up_ne (show (1:Nat) ≠ 22 by omega),
              up_ne (show (1:Nat) ≠ 17 by omega),
              up_ne (show (1:Nat) ≠ 20 by omega),
              up_ne (show (1:Nat) ≠ 20 by omega),
              up_ne (show (1:Nat) ≠ 13 by omega),
              up_ne (show (1:Nat) ≠ 12 by omega), h1])
      (by rw [hG7def, up_ne (show (2:Nat) ≠ 22 by omega),
              up_ne (show (2:Nat) ≠ 22 by omega),
              up_ne (show (2:Nat) ≠ 17 by omega),
              up_ne (show (2:Nat) ≠ 20 by omega),
              up_ne (show (2:Nat) ≠ 20 by omega),
              up_ne (show (2:Nat) ≠ 13 by omega),
              up_ne (show (2:Nat) ≠ 12 by omega), h2])
      (by rw [hG7def, up_ne (show (6:Nat) ≠ 22 by omega),
              up_ne (show (6:Nat) ≠ 22 by omega),
              up_ne (show (6:Nat) ≠ 17 by omega),
              up_ne (show (6:Nat) ≠ 20 by omega),
              up_ne (show (6:Nat) ≠ 20 by omega),
              up_ne (show (6:Nat) ≠ 13 by omega),
              up_ne (show (6:Nat) ≠ 12 by omega), h6])
      (by rw [hG7def, up_ne (show (12:Nat) ≠ 22 by omega),
              up_ne (show (12:Nat) ≠ 22 by omega),
              up_ne (show (12:Nat) ≠ 17 by omega),
              up_ne (show (12:Nat) ≠ 20 by omega),
              up_ne (show (12:Nat) ≠ 20 by omega),
              up_ne (show (12:Nat) ≠ 13 by omega), up_eq])
      (by rw [hG7def, up_ne (show (13:Nat) ≠ 22 by omega),
              up_ne (show (13:Nat) ≠ 22 by omega),
              up_ne (show (13:Nat) ≠ 17 by omega),
              up_ne (show (13:Nat) ≠ 20 by omega),
              up_ne (show (13:Nat) ≠ 20 by omega), up_eq])
      (by rw [hG7def, up_ne (show (17:Nat) ≠ 22 by omega),
              up_ne (show (17:Nat) ≠ 22 by omega), up_eq])
      (by rw [hG7def, up_ne (show (19:Nat) ≠ 22 by omega),
              up_ne (show (19:Nat) ≠ 22 by omega),
              up_ne (show (19:Nat) ≠ 17 by omega),
              up_ne (show (19:Nat) ≠ 20 by omega),
              up_ne (show (19:Nat) ≠ 20 by omega),
              up_ne (show (19:Nat) ≠ 13 by omega),
              up_ne (show (19:Nat) ≠ 12 by omega), h19])
      (by rw [hG7def, up_eq])
      (by omega) (by omega) fit7 henv
      (by intro q hq q' hq'
          rw [hG7def,
            setup7_ne f 0 (bd2 + 2 ^ (n - n / 2)) (3 * n + 23) (3 * n + 24)
              t0 1 (2 ^ (n / 2)) (bd1 + q) (by omega),
            setup7_ne f 0 (bd2 + 2 ^ (n - n / 2)) (3 * n + 23) (3 * n + 24)
              t0 1 (2 ^ (n / 2)) (bd2 + q') (by omega)]
          exact hpair q hq q' hq')
      (by rw [Nat.sub_zero]; omega) (by omega)
  refine ⟨7 + cL, by omega, ?_⟩
  rcases hexL with hexL | ⟨hexL, i', jp', hi', hj1', hjN', hwit⟩
  · exact Or.inl (by rw [hsetup, hexL])
  · refine Or.inr ⟨by rw [hsetup, hexL], ⟨i', jp', hi', hj1', hjN', ?_⟩⟩
    rw [hG7def,
      setup7_ne f 0 (bd2 + 2 ^ (n - n / 2)) (3 * n + 23) (3 * n + 24)
        t0 1 (2 ^ (n / 2)) (bd1 + i') (by omega),
      setup7_ne f 0 (bd2 + 2 ^ (n - n / 2)) (3 * n + 23) (3 * n + 24)
        t0 1 (2 ^ (n / 2)) (bd2 + (jp' - 1)) (by omega)] at hwit
    exact hwit

/-! ## §3. The folded budget: 30 * 2^(n/2) + 9 -/

/-- scanB's phase budget with `2^(n−n/2) ≤ 2·2^(n/2)` folded:
`c ≤ 30 * 2^(n/2) + 9` — the honest constant for `budget_compose2`
(the gap map sketched `30·2^(n/2) + 24`; the landed program is `+9`). -/
theorem scanB_budget {w n : Nat} (ρ : Nat → BitVec w)
    (f : Nat → Nat) (bd1 bd2 t0 : Nat) (r S : Nat)
    (hbd1 : 22 < bd1) (hbd2 : 22 < bd2)
    (hb1 : bd1 + 2 ^ (n / 2) ≤ bd2 + 2 ^ (n - n / 2))
    (hb2 : bd2 + 2 ^ (n - n / 2) ≤ BD2 n + 2 * 2 ^ (n - n / 2) + 1)
    (hw1 : 1 ≤ w)
    (hfit : ∀ q, f q < 2 ^ w)
    (h1 : f 1 = 1) (h2 : f 2 = 0) (h6 : f 6 = bd1) (h7 : f 7 = n)
    (h8 : f 8 = 2 * n + 23) (h9 : f 9 = n / 2)
    (h11 : f 11 = 2 ^ (n - n / 2)) (h19 : f 19 = bd2)
    (ht0 : f (3 * n + 24) = t0)
    (haddr : ∀ c, c ≤ BD2 n + 2 * 2 ^ (n - n / 2) + 1 → c < 2 ^ w)
    (hpair : ∀ q, q < 2 ^ (n / 2) → ∀ q', q' < 2 ^ (n - n / 2) →
      f (bd1 + q) + f (bd2 + q') < 2 ^ w)
    (hS : 30 * 2 ^ (n / 2) + 9 ≤ S) :
    ∃ c, c ≤ 30 * 2 ^ (n / 2) + 9 ∧
      (exec prog2 ρ S 231 r (memOf w f) = some false
        ∨ exec prog2 ρ S 231 r (memOf w f) = some true
          ∧ ∃ i jp, i < 2 ^ (n / 2) ∧ 1 ≤ jp ∧ jp ≤ 2 ^ (n - n / 2) ∧
            f (bd1 + i) + f (bd2 + (jp - 1)) = t0) := by
  have hmh : n - n / 2 ≤ n / 2 + 1 := by omega
  have hpowm : 2 ^ (n - n / 2) ≤ 2 * 2 ^ (n / 2) := by
    have h1 : 2 ^ (n - n / 2) ≤ 2 ^ (n / 2 + 1) :=
      Nat.pow_le_pow_right (by omega) hmh
    have h2 : 2 ^ (n / 2 + 1) = 2 * 2 ^ (n / 2) := by
      rw [Nat.pow_succ]
      omega
    omega
  -- fold 10 * (2^(n/2) + 2^(n−n/2)) ≤ 30 * 2^(n/2) without handing omega
  -- a goal that mixes two distinct pow atoms
  have h5 : 10 * (2 ^ (n / 2) + 2 ^ (n - n / 2)) ≤ 30 * 2 ^ (n / 2) := by
    have h3 : 2 ^ (n / 2) + 2 ^ (n - n / 2) ≤ 2 ^ (n / 2) + 2 * 2 ^ (n / 2) :=
      Nat.add_le_add (Nat.le_refl _) hpowm
    have h4 : 10 * (2 ^ (n / 2) + 2 ^ (n - n / 2))
        ≤ 10 * (2 ^ (n / 2) + 2 * 2 ^ (n / 2)) :=
      Nat.mul_le_mul (Nat.le_refl _) h3
    have h6 : 10 * (2 ^ (n / 2) + 2 * 2 ^ (n / 2)) = 30 * 2 ^ (n / 2) := by
      omega
    rw [h6] at h4
    exact h4
  have hS10 : 10 * (2 ^ (n / 2) + 2 ^ (n - n / 2)) + 9 ≤ S :=
    Nat.le_trans (Nat.add_le_add h5 (Nat.le_refl 9)) hS
  obtain ⟨c, hc, hex⟩ :=
    scanB_exec ρ f bd1 bd2 t0 r S hbd1 hbd2 hb1 hb2 hw1 hfit h1 h2 h6 h7 h8
      h9 h11 h19 ht0 haddr hpair hS10
  exact ⟨c, Nat.le_trans hc (Nat.add_le_add h5 (Nat.le_refl 9)), hex⟩

end SubsetSum.MITM

#print axioms SubsetSum.MITM.scanLoop_exec
#print axioms SubsetSum.MITM.scanB_exec
#print axioms SubsetSum.MITM.scanB_budget
