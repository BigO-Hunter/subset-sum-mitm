import Submission.PhaseA
import Submission.Sort
set_option autoImplicit true
set_option maxHeartbeats 12000000

/-!
# Phase A2: the v2 second-half merge (v2 PH2) + entry plumbing (v2 M2)

§0 `BD2 n` — the second-half base; pow helpers; shifted word-fit.
§1 `AReg2 n` — phaseA2's write region (M2, window amended by PH2: the
   upper strip's last cell `BD2 + 2^(m2+1)` *is* written when the final
   round lands on the upper strip, so the window carries the separator
   cell: `[BD2, BD2 + 2^(n−n/2+1) + 1)`).
§2 `hrel2_of_pres`, `block_not_AReg2`, `bd1_not_AReg2` (M2 + PH2).
§3 `lswap2_exec` — the L2SWAP tail: loads `n+1` (from cell 7) into 21.
§4 `diLoop2_exec` / `djLoop2_exec` / `merge2_exec` — the merge loops at
   pcs 191/199/169 → 207 (phaseA's loops shifted by +66; the round body
   of `phaseA2` is byte-identical to `phaseA`'s, targets included).
§5 `round2_exec` — one round 164 → 213; the source family is the second
   half `fun i => instA x (n / 2 + i)`, the round counter in cell 10 is
   GLOBAL (`n/2 + k`), the guard bound is `n+1`, and `Pres (AReg2 n)`.
§6 `lround2_exec` — the fuel driver 164 → 215.
§7 `phaseA2_exec` — the phase driver 148 → 215 (PH2).
-/

namespace SubsetSum.MITM

open BigOSpeedrun.SubsetSum SubsetSum.MITM.Spec

/-! ## §0. The second-half base and helpers -/

/-- The second-half array base: `3n+25+2^(n/2+1)+2`, one cell above
phaseA's two first-half strips. -/
def BD2 (n : Nat) : Nat := 3 * n + 25 + 2 * 2 ^ (n / 2) + 2

/-- Every second-half family half-sum plus its addend fits in a word
(shifted twin of `halfSumAddFit`). -/
theorem halfSumAddFit2 {n w : Nat} {x : Instance n} (hn : 2 ≤ n)
    (hw : wordLength n x.bits ≤ w) (q : Nat) (hq : q < n - n / 2)
    (v : Nat) (hv : v ∈ halfSums (fun i => instA x (n / 2 + i)) q) :
    v + instA x (n / 2 + q) < 2 ^ w := by
  have hsum : 2 * ((List.range n).map (instA x)).sum
      < 2 ^ (wordLength n x.bits) := two_sum_lt_pow_wordLength x hn
  have hvle : v ≤ ((List.range q).map (fun i => instA x (n / 2 + i))).sum :=
    halfSumsLe _ _ _ hv
  have hqle : ((List.range q).map (fun i => instA x (n / 2 + i))).sum
      ≤ ((List.range (n - n / 2)).map (fun i => instA x (n / 2 + i))).sum :=
    sumRangeMono _ (by omega)
  have hsplit : ((List.range (n / 2 + (n - n / 2))).map (instA x)).sum
      = ((List.range (n / 2)).map (instA x)).sum
        + ((List.range (n - n / 2)).map (fun i => instA x (n / 2 + i))).sum :=
    sum_split_shift (instA x) (n - n / 2) (n / 2)
  have hn2 : n / 2 + (n - n / 2) = n := by omega
  rw [hn2] at hsplit
  have hmem : instA x (n / 2 + q) ∈ (List.range n).map (instA x) :=
    List.mem_map.mpr ⟨n / 2 + q, List.mem_range.mpr (by omega), rfl⟩
  have haddle := memLeSum hmem
  have hpow : 2 ^ (wordLength n x.bits) ≤ 2 ^ w :=
    Nat.pow_le_pow_right (n := 2) (by omega) hw
  omega

/-- Move a `≤ B - C` goal into addition form (omega atomizes compound
RHS-subtractions like `≤ S - (c1 + 1)` and refuses to link them to `B`/`C`). -/
theorem sub_le_of_add_le (A B C : Nat) (h : A + C ≤ B) : A ≤ B - C := by omega

/-- `s + 1 ≤ 2 ^ s` for every `s`. -/
theorem succ_le_two_pow (s : Nat) : s + 1 ≤ 2 ^ s := by
  induction s with
  | zero => omega
  | succ s ih =>
    rw [Nat.pow_succ]
    have h : (2:Nat) * (s + 1) = s + 1 + (s + 1) := by omega
    omega

/-- Round-cost bound lifts to the next power form. -/
theorem c1_step (x b : Nat) (h : x ≤ 44 * b + 23) : x + 1 ≤ 44 * b + 24 := by omega

/-- Trivial bound for the exit-branch `arrL_up_out` argument. -/
theorem d33_lt (d q : Nat) (h : 33 ≤ d) : 19 < d + q := by omega

/-- `(k + 1) - 1 = k`. -/
theorem sub1 (k : Nat) : (k + 1) - 1 = k := by omega

/-- `a < b` gives `a + 1 ≤ b`. -/
theorem lt_succ_le (a b : Nat) (h : a < b) : a + 1 ≤ b := by omega

/-- Split a `44 * (X - 2 ^ k)` compound (needs `2 ^ k ≤ X`). -/
theorem h44split (X k : Nat) (h : 2 ^ k ≤ X) :
    44 * (X - 2 ^ k) = 44 * X - 44 * 2 ^ k := by omega

/-- The lround2 ih-budget step: the round-`(k+1)` budget follows from the
round-`k` budget, the round cost `c1 ≤ 44·2^(k−1) + 23`. -/
theorem ih_budget_step (B k Mp S' c1 : Nat)
    (h2k : 2 ^ k = 2 * 2 ^ (k - 1)) (hk2m : 2 ^ k ≤ 2 ^ B) (hkm : k + 1 ≤ Mp)
    (hc1 : c1 ≤ 44 * 2 ^ (k - 1) + 23)
    (hS : 44 * (2 ^ B - 2 ^ (k - 1)) + 24 * (Mp - k + 1) + 1 ≤ S') :
    44 * (2 ^ B - 2 ^ k) + 24 * (Mp - (k + 1) + 1) + 1 ≤ S' - (c1 + 1) := by
  have h24le : 24 * (Mp - (k + 1) + 1) ≤ 24 * (Mp - k + 1) := by omega
  have hc1' : c1 + 1 ≤ 44 * 2 ^ (k - 1) + 24 := c1_step c1 (2 ^ (k - 1)) hc1
  refine sub_le_of_add_le _ _ _ ?_
  omega

/-! ## §1. The phaseA2 write region -/

/-- phaseA2's write region: registers (cells ≤ 22) plus the second-half
strips above the first-half arrays (two strips of `2^(n−n/2)` cells plus
the one-cell separator). -/
def AReg2 (n : Nat) (c : Nat) : Prop :=
  c ≤ 22 ∨ (3 * n + 25 + 2 * 2 ^ (n / 2) + 2 ≤ c ∧
    c < 3 * n + 25 + 2 * 2 ^ (n / 2) + 2 + 2 * 2 ^ (n - n / 2) + 1)

/-! ## §2. Source-address facts (PH2's `hrel2`) and exclusions -/

/-- `hrel2` discharged from `Pres` + relocation: phaseA preserves the
relocated input block, and the second-half family reads it at the
`n/2`-shifted index. -/
theorem hrel2_of_pres {n : Nat} {f0 f' : Nat → Nat} {x : Instance n}
    (hn : 2 ≤ n) (hpres : Pres (AReg n) f0 f')
    (hrel : ∀ i, 1 ≤ i → i ≤ n → f0 (2 * n + 23 + i) = instA x (i - 1)) :
    ∀ i, 1 ≤ i → i ≤ n - n / 2 →
      f' (2 * n + 23 + n / 2 + i) = instA x (n / 2 + i - 1) := by
  intro i hi1 hi2
  have hnA : ¬ AReg n (2 * n + 23 + (n / 2 + i)) := by
    intro hA
    have hc : 2 * n + 23 + n / 2 + i ≤ 3 * n + 23 := by omega
    rcases hA with hA | ⟨hle, _⟩
    · omega
    · omega
  rw [show 2 * n + 23 + n / 2 + i = 2 * n + 23 + (n / 2 + i) from by omega]
  rw [hpres _ hnA]
  exact hrel (n / 2 + i) (by omega) (by omega)

/-- The relocated input block (and the `t` cell `RELOC+n+1 = 3n+24`)
lies outside `AReg2 n`: with `2 ≤ n` the block sits above the register
file and strictly below the first-half arrays. -/
theorem block_not_AReg2 {n c : Nat} (hn : 2 ≤ n)
    (h1 : 2 * n + 23 < c) (h2 : c < 3 * n + 25) : ¬ AReg2 n c := by
  intro hA
  have hc : 3 * n + 27 ≤ c := by
    rcases hA with hA | ⟨hle, _⟩
    · omega
    · have hX : 0 ≤ 2 ^ (n / 2 + 1) := Nat.zero_le _
      omega
  omega

/-- Either first-half base lies outside `AReg2 n` (the second-half
window starts at `BD2 n = 3n+25+2^(n/2+1)+2`). -/
theorem bd1_not_AReg2 {n c : Nat} (hn : 2 ≤ n)
    (h : c = 3 * n + 25 ∨ c = 3 * n + 25 + 2 ^ (n / 2) + 1) : ¬ AReg2 n c := by
  intro hA
  have h1le : (1:Nat) ≤ 2 ^ (n / 2) := Nat.one_le_two_pow
  rcases hA with hA | ⟨hle, _⟩ <;> rcases h with rfl | rfl <;> omega

/-- Cells written by phaseA2/canon/scanB outside the register file all
sit in `AReg2 n`'s second strip window; in particular the second-half
strips are inside it. -/
theorem strip_in_AReg2 {n c : Nat} (hn : 2 ≤ n) (hc1 : BD2 n ≤ c)
    (hc2 : c < BD2 n + 2 * 2 ^ (n - n / 2) + 1) : AReg2 n c := by
  have hBD : BD2 n = 3 * n + 25 + 2 * 2 ^ (n / 2) + 2 := rfl
  rw [hBD] at hc1 hc2
  exact Or.inr ⟨hc1, hc2⟩


/-! ## §3. The LSWAP tail (pc 207 → 213). -/

/-- The LSWAP tail (pc 141–146): double `L`, swap the array pointers,
bump `k`, load the bound `n+1` (from cell 7) into cell 21. -/
theorem lswap2_exec {w : Nat} {P : List Instr} {ρ : Nat → BitVec w} {f : Nat → Nat}
    {S r pc L b d k : Nat}
    (h11 : f 11 = L) (h1 : f 1 = 1) (h2 : f 2 = 0) (h7 : f 7 = n)
    (h10 : f 10 = k) (h18 : f 18 = b) (h19 : f 19 = d)
    (c1 : P.getD pc Instr.reject = Instr.add 11 11 11)
    (c2 : P.getD (pc + 1) Instr.reject = Instr.add 20 18 2)
    (c3 : P.getD (pc + 2) Instr.reject = Instr.add 18 19 2)
    (c4 : P.getD (pc + 3) Instr.reject = Instr.add 19 20 2)
    (c5 : P.getD (pc + 4) Instr.reject = Instr.add 10 10 1)
    (c6 : P.getD (pc + 5) Instr.reject = Instr.add 21 7 1)
    (hS : 6 ≤ S) :
    exec P ρ S pc r (memOf w f)
      = exec P ρ (S - 6) (pc + 6) r
          (memOf w (up (up (up (up (up (up f 11 (2 * L)) 20 b) 18 d) 19 b)
            10 (k + 1)) 21 (n + 1))) := by
  rw [exec_add_step (by omega) c1,
      show f 11 + f 11 = 2 * L from by omega,
      exec_add_step (by omega) c2,
      show (up f 11 (2 * L)) 18 + (up f 11 (2 * L)) 2 = b from by
        rw [up_ne (show (18:Nat) ≠ 11 by omega),
            up_ne (show (2:Nat) ≠ 11 by omega), h18, h2, Nat.add_zero],
      exec_add_step (by omega) c3,
      show (up (up f 11 (2 * L)) 20 b) 19 + (up (up f 11 (2 * L)) 20 b) 2 = d from by
        rw [up_ne (show (19:Nat) ≠ 20 by omega),
            up_ne (show (19:Nat) ≠ 11 by omega),
            up_ne (show (2:Nat) ≠ 20 by omega),
            up_ne (show (2:Nat) ≠ 11 by omega), h19, h2, Nat.add_zero],
      exec_add_step (by omega) c4,
      show (up (up (up f 11 (2 * L)) 20 b) 18 d) 20
          + (up (up (up f 11 (2 * L)) 20 b) 18 d) 2 = b from by
        rw [up_ne (show (20:Nat) ≠ 18 by omega), up_eq,
            up_ne (show (2:Nat) ≠ 18 by omega),
            up_ne (show (2:Nat) ≠ 20 by omega),
            up_ne (show (2:Nat) ≠ 11 by omega), h2, Nat.add_zero],
      exec_add_step (by omega) c5,
      show (up (up (up (up f 11 (2 * L)) 20 b) 18 d) 19 b) 10
          + (up (up (up (up f 11 (2 * L)) 20 b) 18 d) 19 b) 1 = k + 1 from by
        rw [up_ne (show (10:Nat) ≠ 19 by omega),
            up_ne (show (10:Nat) ≠ 18 by omega),
            up_ne (show (10:Nat) ≠ 20 by omega),
            up_ne (show (10:Nat) ≠ 11 by omega), h10,
            up_ne (show (1:Nat) ≠ 19 by omega),
            up_ne (show (1:Nat) ≠ 18 by omega),
            up_ne (show (1:Nat) ≠ 20 by omega),
            up_ne (show (1:Nat) ≠ 11 by omega), h1],
      exec_add_step (by omega) c6,
      show (up (up (up (up (up f 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 7
          + (up (up (up (up (up f 11 (2 * L)) 20 b) 18 d) 19 b) 10 (k + 1)) 1
          = n + 1 from by
        rw [up_ne (show (7:Nat) ≠ 10 by omega),
            up_ne (show (7:Nat) ≠ 19 by omega),
            up_ne (show (7:Nat) ≠ 18 by omega),
            up_ne (show (7:Nat) ≠ 20 by omega),
            up_ne (show (7:Nat) ≠ 11 by omega), h7,
            up_ne (show (1:Nat) ≠ 10 by omega),
            up_ne (show (1:Nat) ≠ 19 by omega),
            up_ne (show (1:Nat) ≠ 18 by omega),
            up_ne (show (1:Nat) ≠ 20 by omega),
            up_ne (show (1:Nat) ≠ 11 by omega), h1]]
  simp only [Nat.sub_sub, Nat.reduceAdd]

/-! ## §4. The merge loops (pcs 191/199/169 → 207). -/

/-- Drain-i body loop (pc 125 → 141). -/
theorem diLoop2_exec {w : Nat} (ρ : Nat → BitVec w) :
    ∀ (N L b d : Nat) (sl out : List Nat) (f : Nat → Nat) (i wq S r : Nat),
    sl.length = L →
    i < L → wq = L + i → f 12 = i → f 14 = wq → f 11 = L →
    f 18 = b → f 19 = d → f 1 = 1 → f 2 = 0 →
    (∀ q, q < L → f (b + q) = sl.getD q 0) →
    (∀ v ∈ sl, v < 2 ^ w) →
    (out.take wq = (arrL f d (2 * L)).take wq) →
    out.drop wq = sl.drop i →
    (∀ q, f q < 2 ^ w) → b + L < 2 ^ w → d + 2 * L < 2 ^ w → 2 * L < 2 ^ w →
    33 ≤ b → 33 ≤ d → (∀ p q, p < 2 * L → q < L → d + p ≠ b + q) →
    L - i ≤ N → 8 * N + 9 ≤ S →
    ∃ c f', c ≤ 8 * N + 9 ∧
      exec prog2 ρ S 191 r (memOf w f) = exec prog2 ρ (S - c) 207 r (memOf w f') ∧
      arrL f' d (2 * L) = out ∧ f' 12 = L ∧ f' 14 = 2 * L ∧
      (∀ q, f' q < 2 ^ w) ∧ Pres (MReg d L) f f' := by
  intro N
  induction N with
  | zero =>
    intro L b d sl out f i wq S r hsL hiL hwi hf12 hf14 hf11 hf18 hf19 h1 h2
      hsrc hvfit htake hdrop hfit hbL hdL h2L hb33 hd33 hdisj hN hS
    omega
  | succ N ih =>
    intro L b d sl out f i wq S r hsL hiL hwi hf12 hf14 hf11 hf18 hf19 h1 h2
      hsrc hvfit htake hdrop hfit hbL hdL h2L hb33 hd33 hdisj hN hS
    have hvsl : sl.getD i 0 < 2 ^ w := hvfit _ (mem_getD (by omega))
    have fi1 : ∀ q, (up f 20 (b + i)) q < 2 ^ w := up_fit hfit (by have := hbL; omega)
    have fi2 : ∀ q, (up (up f 20 (b + i)) 15 (sl.getD i 0)) q < 2 ^ w := up_fit fi1 (by omega)
    have fi3 : ∀ q, (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) q < 2 ^ w := up_fit fi2 (by have := hdL; omega)
    have fi4 : ∀ q, (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) q < 2 ^ w := up_fit fi3 (by omega)
    have fi5 : ∀ q, (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) q < 2 ^ w := up_fit fi4 (by omega)
    have fi6 : ∀ q, (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) q < 2 ^ w := up_fit fi5 (by omega)
    -- array views
    have hA2 : arrL (up (up f 20 (b + i)) 15 (sl.getD i 0)) d (2 * L) = arrL f d (2 * L) := by
      rw [show arrL (up (up f 20 (b + i)) 15 (sl.getD i 0)) d (2 * L) = arrL (up f 20 (b + i)) d (2 * L) from
          arrL_up_out (fun q _ => show (15:Nat) ≠ d + q by omega),
        show arrL (up f 20 (b + i)) d (2 * L) = arrL f d (2 * L) from
          arrL_up_out (fun q _ => show (20:Nat) ≠ d + q by omega)]
    have hA3 : arrL (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) d (2 * L) = arrL f d (2 * L) := by
      rw [show arrL (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) d (2 * L) = arrL (up (up f 20 (b + i)) 15 (sl.getD i 0)) d (2 * L) from
          arrL_up_out (fun q _ => show (21:Nat) ≠ d + q by omega), hA2]
    have hA6 : arrL (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) d (2 * L) = arrL (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) d (2 * L) := by
      rw [show arrL (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) d (2 * L) = arrL (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) d (2 * L) from
          arrL_up_out (fun q _ => show (14:Nat) ≠ d + q by omega),
        show arrL (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) d (2 * L) = arrL (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) d (2 * L) from
          arrL_up_out (fun q _ => show (12:Nat) ≠ d + q by omega)]
    have hleno : out.length = 2 * L := by
      have h1l := List.length_drop (l := out) (i := wq)
      rw [hdrop, List.length_drop (l := sl) (i := i)] at h1l
      omega
    -- list facts
    have hisl : i < sl.length := by omega
    have hwqo : wq < out.length := by omega
    have hwq2L : wq < 2 * L := by omega
    have htake1 : out.take (wq + 1) = (arrL (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) d (2 * L)).take (wq + 1) := by
      rw [hA6, arrL_take_up hwq2L, hA3, ← htake, takeSucc hwqo]
      congr 1
      rw [← getDDrop, hdrop, dropCons hisl]
      simp
    have hdrop1 : out.drop (wq + 1) = sl.drop (i + 1) := by
      rw [dropSucc, hdrop, dropCons hisl]
      simp
    -- G6 register facts
    have e12g : (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 12 = i + 1 := by
      rw [up_ne (show (12:Nat) ≠ 14 by omega), up_eq]
    have e14g : (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 14 = wq + 1 := up_eq _ _ _
    have e11g : (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 11 = L := by rw [up_ne (show (11:Nat) ≠ 14 by omega), up_ne (show (11:Nat) ≠ 12 by omega), up_ne (show (11:Nat) ≠ d + wq by omega), up_ne (show (11:Nat) ≠ 21 by omega), up_ne (show (11:Nat) ≠ 15 by omega), up_ne (show (11:Nat) ≠ 20 by omega), hf11]
    have e18g : (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 18 = b := by rw [up_ne (show (18:Nat) ≠ 14 by omega), up_ne (show (18:Nat) ≠ 12 by omega), up_ne (show (18:Nat) ≠ d + wq by omega), up_ne (show (18:Nat) ≠ 21 by omega), up_ne (show (18:Nat) ≠ 15 by omega), up_ne (show (18:Nat) ≠ 20 by omega), hf18]
    have e19g : (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 19 = d := by rw [up_ne (show (19:Nat) ≠ 14 by omega), up_ne (show (19:Nat) ≠ 12 by omega), up_ne (show (19:Nat) ≠ d + wq by omega), up_ne (show (19:Nat) ≠ 21 by omega), up_ne (show (19:Nat) ≠ 15 by omega), up_ne (show (19:Nat) ≠ 20 by omega), hf19]
    have e1g : (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 1 = 1 := by rw [up_ne (show (1:Nat) ≠ 14 by omega), up_ne (show (1:Nat) ≠ 12 by omega), up_ne (show (1:Nat) ≠ d + wq by omega), up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 15 by omega), up_ne (show (1:Nat) ≠ 20 by omega), h1]
    have e2g : (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 2 = 0 := by rw [up_ne (show (2:Nat) ≠ 14 by omega), up_ne (show (2:Nat) ≠ 12 by omega), up_ne (show (2:Nat) ≠ d + wq by omega), up_ne (show (2:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 15 by omega), up_ne (show (2:Nat) ≠ 20 by omega), h2]
    have esrcg : ∀ q, q < L → (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) (b + q) = sl.getD q 0 := by
      intro q hq
      rw [up_ne (show b + q ≠ 14 by omega),
        up_ne (show b + q ≠ 12 by omega),
        up_ne (Ne.symm (hdisj wq q (by omega) hq)),
        up_ne (show b + q ≠ 21 by omega),
        up_ne (show b + q ≠ 15 by omega), up_ne (show b + q ≠ 20 by omega)]
      exact hsrc q hq
    -- the shared 7-step prefix (125..130) with inline normalization
    have hsteps : exec prog2 ρ S 191 r (memOf w f)
        = exec prog2 ρ (S - 6) 197 r (memOf w (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1))) := by
      rw [exec_add_step (by omega)
          (show prog2.getD 191 Instr.reject = Instr.add 20 18 12 by rfl),
          show f 18 + f 12 = b + i from by rw [hf18, hf12],
        exec_load_step (by omega)
          (show prog2.getD 192 Instr.reject = Instr.load 15 20 by rfl) fi1,
          up_eq, up_ne (show b + i ≠ 20 by omega), hsrc i hiL,
        exec_add_step (by omega)
          (show prog2.getD 193 Instr.reject = Instr.add 21 19 14 by rfl),
          show (up (up f 20 (b + i)) 15 (sl.getD i 0)) 19 + (up (up f 20 (b + i)) 15 (sl.getD i 0)) 14 = d + wq from by
            rw [up_ne (show (19:Nat) ≠ 15 by omega),
              up_ne (show (14:Nat) ≠ 15 by omega),
              up_ne (show (19:Nat) ≠ 20 by omega),
              up_ne (show (14:Nat) ≠ 20 by omega), hf19, hf14],
        exec_store_step (by omega)
          (show prog2.getD 194 Instr.reject = Instr.store 21 15 by rfl) fi3,
          up_eq, up_ne (show (15:Nat) ≠ 21 by omega), up_eq,
        exec_add_step (by omega)
          (show prog2.getD 195 Instr.reject = Instr.add 12 12 1 by rfl),
          show (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 + (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 1 = i + 1 from by
            rw [up_ne (show (12:Nat) ≠ d + wq by omega),
              up_ne (show (12:Nat) ≠ 21 by omega), up_ne (show (12:Nat) ≠ 15 by omega),
              up_ne (show (12:Nat) ≠ 20 by omega), hf12,
              up_ne (show (1:Nat) ≠ d + wq by omega),
              up_ne (show (1:Nat) ≠ 21 by omega),
              up_ne (show (1:Nat) ≠ 15 by omega),
              up_ne (show (1:Nat) ≠ 20 by omega), h1],
        exec_add_step (by omega)
          (show prog2.getD 196 Instr.reject = Instr.add 14 14 1 by rfl),
          show (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 + (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 1 = wq + 1 from by
            rw [up_ne (show (14:Nat) ≠ 12 by omega),
              up_ne (show (14:Nat) ≠ d + wq by omega),
              up_ne (show (14:Nat) ≠ 21 by omega),
              up_ne (show (14:Nat) ≠ 15 by omega),
              up_ne (show (14:Nat) ≠ 20 by omega), hf14,
              up_ne (show (1:Nat) ≠ 12 by omega),
              up_ne (show (1:Nat) ≠ d + wq by omega),
              up_ne (show (1:Nat) ≠ 21 by omega),
              up_ne (show (1:Nat) ≠ 15 by omega),
              up_ne (show (1:Nat) ≠ 20 by omega), h1]]
      simp only [Nat.sub_sub, Nat.reduceAdd]
    by_cases hnext : i + 1 < L
    · have h131 : (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 12 < (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 11 := by

        rw [e12g, e11g]
        exact hnext
      rw [hsteps, exec_blt_lt_step (by omega)
        (show prog2.getD 197 Instr.reject = Instr.blt 12 11 191 by rfl) fi6 h131]
      obtain ⟨c2, f2, hc2, hex2, harr2, h122, h142, hfit2, hpres2⟩ :=
        ih L b d sl out (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) (i + 1) (wq + 1) (S - 7) r hsL hnext (by omega)
          e12g e14g e11g e18g e19g e1g e2g esrcg hvfit htake1 hdrop1 fi6 hbL hdL
          h2L hb33 hd33 hdisj (by omega) (by omega)
      refine ⟨7 + c2, f2, by omega, ?_, harr2, h122, h142, hfit2, ?_⟩
      · have hS7 : S - 6 - 1 = S - 7 := by omega
        have hS2 : S - 7 - c2 = S - (7 + c2) := by omega
        rw [hS7, hex2, hS2]
      · have q1 : Pres (MReg d L) f (up f 20 (b + i)) :=
          pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
        have q2 : Pres (MReg d L) (up f 20 (b + i)) (up (up f 20 (b + i)) 15 (sl.getD i 0)) :=
          pres_up (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        have q3 : Pres (MReg d L) (up (up f 20 (b + i)) 15 (sl.getD i 0)) (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) :=
          pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
        have q4 : Pres (MReg d L) (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) := pres_up (MReg_dst (by omega) (by omega))
        have q5 : Pres (MReg d L) (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) := pres_up (Or.inl rfl)
        have q6 : Pres (MReg d L) (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) :=
          pres_up (Or.inr (Or.inr (Or.inl rfl)))
        exact pres_trans q1 (pres_trans q2 (pres_trans q3 (pres_trans q4
          (pres_trans q5 (pres_trans q6 hpres2)))))
    · have h131 : ¬ (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 12 < (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 11 := by

        rw [e12g, e11g]
        omega
      have h132 : (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 2 < (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) 1 := by rw [e2g, e1g]; omega
      have hrw2 : exec prog2 ρ S 191 r (memOf w f)
          = exec prog2 ρ (S - 8) 207 r (memOf w (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1))) := by
        rw [hsteps,
          exec_blt_ge_step (by omega)
            (show prog2.getD 197 Instr.reject = Instr.blt 12 11 191 by rfl) fi6 h131,
          exec_blt_lt_step (by omega)
            (show prog2.getD 198 Instr.reject = Instr.blt 2 1 207 by rfl) fi6 h132]
        simp only [Nat.sub_sub, Nat.reduceAdd]
      have hfull : arrL (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) d (2 * L) = out := by
        have hq2 : wq + 1 = 2 * L := by omega
        rw [hq2] at htake1
        have hto := takeAll (l := out) (n := 2 * L) (by omega)
        have hla : (arrL (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) d (2 * L)).length = 2 * L := by simp [arrL]
        have hta := takeAll (l := arrL (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) d (2 * L)) (n := 2 * L) (by omega)
        rw [← hta, ← hto, htake1, hq2]
      refine ⟨8, (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)), by omega, hrw2, hfull, by rw [e12g]; omega,
        by rw [e14g]; omega, fi6, ?_⟩
      have q1 : Pres (MReg d L) f (up f 20 (b + i)) :=
        pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      have q2 : Pres (MReg d L) (up f 20 (b + i)) (up (up f 20 (b + i)) 15 (sl.getD i 0)) :=
        pres_up (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      have q3 : Pres (MReg d L) (up (up f 20 (b + i)) 15 (sl.getD i 0)) (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) :=
        pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
      have q4 : Pres (MReg d L) (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) := pres_up (MReg_dst (by omega) (by omega))
      have q5 : Pres (MReg d L) (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) := pres_up (Or.inl rfl)
      exact pres_trans q1 (pres_trans q2 (pres_trans q3 (pres_trans q4
        (pres_trans q5 (pres_up (Or.inr (Or.inr (Or.inl rfl))))))))

theorem djLoop2_exec {w : Nat} (ρ : Nat → BitVec w) :
    ∀ (N L b d ak : Nat) (sl out : List Nat) (f : Nat → Nat) (j wq S r : Nat),
    sl.length = L →
    j < L → wq = L + j → f 12 = L → f 13 = j → f 14 = wq → f 11 = L →
    f 17 = ak → f 18 = b → f 19 = d → f 1 = 1 → f 2 = 0 →
    (∀ q, q < L → f (b + q) = sl.getD q 0) →
    (∀ v ∈ sl, v + ak < 2 ^ w) →
    (out.take wq = (arrL f d (2 * L)).take wq) →
    out.drop wq = (sl.map (fun z => z + ak)).drop j →
    (∀ q, f q < 2 ^ w) → b + L < 2 ^ w → d + 2 * L < 2 ^ w → 2 * L < 2 ^ w →
    33 ≤ b → 33 ≤ d → (∀ p q, p < 2 * L → q < L → d + p ≠ b + q) →
    L - j ≤ N → 8 * N + 8 ≤ S →
    ∃ c f', c ≤ 8 * N + 8 ∧
      exec prog2 ρ S 199 r (memOf w f) = exec prog2 ρ (S - c) 207 r (memOf w f') ∧
      arrL f' d (2 * L) = out ∧ f' 12 = L ∧ f' 13 = L ∧ f' 14 = 2 * L ∧
      (∀ q, f' q < 2 ^ w) ∧ Pres (MReg d L) f f' := by
  intro N
  induction N with
  | zero =>
    intro L b d ak sl out f j wq S r hsL hjL hwj hf12 hf13 hf14 hf11 hf17 hf18
      hf19 h1 h2 hsrc hvfit htake hdrop hfit hbL hdL h2L hb33 hd33 hdisj hN hS
    exact absurd hN (by omega)
  | succ N ih =>
    intro L b d ak sl out f j wq S r hsL hjL hwj hf12 hf13 hf14 hf11 hf17 hf18
      hf19 h1 h2 hsrc hvfit htake hdrop hfit hbL hdL h2L hb33 hd33 hdisj hN hS
    have hvj : sl.getD j 0 + ak < 2 ^ w := hvfit _ (mem_getD (by omega))
    have fi1 : ∀ q, (up f 21 (b + j)) q < 2 ^ w := up_fit hfit (by have := hbL; omega)
    have fi2 : ∀ q, (up (up f 21 (b + j)) 16 (sl.getD j 0)) q < 2 ^ w := up_fit fi1 (by omega)
    have fi3 : ∀ q, (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) q < 2 ^ w := up_fit fi2 hvj
    have fi4 : ∀ q, (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) q < 2 ^ w := up_fit fi3 (by have := hdL; omega)
    have fi5 : ∀ q, (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) q < 2 ^ w := up_fit fi4 (by omega)
    have fi6 : ∀ q, (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) q < 2 ^ w := up_fit fi5 (by omega)
    have fi7 : ∀ q, (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) q < 2 ^ w := up_fit fi6 (by omega)
    have hA4 : arrL (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) d (2 * L) = arrL f d (2 * L) := by
      rw [show arrL (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) d (2 * L) = arrL (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) d (2 * L) from
          arrL_up_out (fun q _ => show (20:Nat) ≠ d + q by omega),
        show arrL (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) d (2 * L) = arrL (up (up f 21 (b + j)) 16 (sl.getD j 0)) d (2 * L) from
          arrL_up_out (fun q _ => show (16:Nat) ≠ d + q by omega),
        show arrL (up (up f 21 (b + j)) 16 (sl.getD j 0)) d (2 * L) = arrL (up f 21 (b + j)) d (2 * L) from
          arrL_up_out (fun q _ => show (16:Nat) ≠ d + q by omega),
        show arrL (up f 21 (b + j)) d (2 * L) = arrL f d (2 * L) from
          arrL_up_out (fun q _ => show (21:Nat) ≠ d + q by omega)]
    have hA7 : arrL (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) d (2 * L) = arrL (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) d (2 * L) := by
      rw [show arrL (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) d (2 * L) = arrL (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) d (2 * L) from
          arrL_up_out (fun q _ => show (14:Nat) ≠ d + q by omega),
        show arrL (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) d (2 * L) = arrL (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) d (2 * L) from
          arrL_up_out (fun q _ => show (13:Nat) ≠ d + q by omega)]
    have hMlen : (sl.map (fun z => z + ak)).length = L := by
      simp [List.length_map, hsL]
    have hleno : out.length = 2 * L := by
      have h1l := List.length_drop (l := out) (i := wq)
      rw [hdrop] at h1l
      rw [List.length_drop (l := sl.map (fun z => z + ak)) (i := j)] at h1l
      have : (sl.map (fun z => z + ak)).length = L := hMlen
      omega
    have hjM : j < (sl.map (fun z => z + ak)).length := by omega
    have hjl : j < sl.length := by omega
    have hjm : j < (sl.map (fun z => z + ak)).length := by
      simp [List.length_map, hsL]
      omega
    have hdrop1 : out.drop (wq + 1) = (sl.map (fun z => z + ak)).drop (j + 1) := by
      rw [dropSucc, hdrop, dropCons hjM, getD_map_add sl ak j hjl]
      simp
    have hwqo : wq < out.length := by omega
    have hwq2L : wq < 2 * L := by omega
    have htake1 : out.take (wq + 1) = (arrL (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) d (2 * L)).take (wq + 1) := by
      rw [hA7, arrL_take_up hwq2L, hA4, ← htake, takeSucc hwqo]
      congr 1
      rw [← getDDrop, hdrop, dropCons hjM, getD_map_add sl ak j hjl]
      rfl
    -- register facts on T7
    have e13g : (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 13 = j + 1 := by
      rw [up_ne (show (13:Nat) ≠ 14 by omega), up_eq]
    have e14g : (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 14 = wq + 1 := up_eq _ _ _
    have e11g : (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 11 = L := by rw [up_ne (show (11:Nat) ≠ 14 by omega), up_ne (show (11:Nat) ≠ 13 by omega), up_ne (show (11:Nat) ≠ d + wq by omega), up_ne (show (11:Nat) ≠ 20 by omega), up_ne (show (11:Nat) ≠ 16 by omega), up_ne (show (11:Nat) ≠ 16 by omega), up_ne (show (11:Nat) ≠ 21 by omega), hf11]
    have e12g : (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 12 = L := by
      rw [up_ne (show (12:Nat) ≠ 14 by omega), up_ne (show (12:Nat) ≠ 13 by omega), up_ne (show (12:Nat) ≠ d + wq by omega), up_ne (show (12:Nat) ≠ 20 by omega), up_ne (show (12:Nat) ≠ 16 by omega), up_ne (show (12:Nat) ≠ 16 by omega), up_ne (show (12:Nat) ≠ 21 by omega), hf12]
    have e17g : (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 17 = ak := by
      rw [up_ne (show (17:Nat) ≠ 14 by omega), up_ne (show (17:Nat) ≠ 13 by omega), up_ne (show (17:Nat) ≠ d + wq by omega), up_ne (show (17:Nat) ≠ 20 by omega), up_ne (show (17:Nat) ≠ 16 by omega), up_ne (show (17:Nat) ≠ 16 by omega), up_ne (show (17:Nat) ≠ 21 by omega), hf17]
    have e18g : (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 18 = b := by rw [up_ne (show (18:Nat) ≠ 14 by omega), up_ne (show (18:Nat) ≠ 13 by omega), up_ne (show (18:Nat) ≠ d + wq by omega), up_ne (show (18:Nat) ≠ 20 by omega), up_ne (show (18:Nat) ≠ 16 by omega), up_ne (show (18:Nat) ≠ 16 by omega), up_ne (show (18:Nat) ≠ 21 by omega), hf18]
    have e19g : (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 19 = d := by rw [up_ne (show (19:Nat) ≠ 14 by omega), up_ne (show (19:Nat) ≠ 13 by omega), up_ne (show (19:Nat) ≠ d + wq by omega), up_ne (show (19:Nat) ≠ 20 by omega), up_ne (show (19:Nat) ≠ 16 by omega), up_ne (show (19:Nat) ≠ 16 by omega), up_ne (show (19:Nat) ≠ 21 by omega), hf19]
    have e1g : (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 1 = 1 := by rw [up_ne (show (1:Nat) ≠ 14 by omega), up_ne (show (1:Nat) ≠ 13 by omega), up_ne (show (1:Nat) ≠ d + wq by omega), up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 16 by omega), up_ne (show (1:Nat) ≠ 16 by omega), up_ne (show (1:Nat) ≠ 21 by omega), h1]
    have e2g : (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 2 = 0 := by rw [up_ne (show (2:Nat) ≠ 14 by omega), up_ne (show (2:Nat) ≠ 13 by omega), up_ne (show (2:Nat) ≠ d + wq by omega), up_ne (show (2:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 16 by omega), up_ne (show (2:Nat) ≠ 16 by omega), up_ne (show (2:Nat) ≠ 21 by omega), h2]
    have hdisj2 : ∀ q, q < L → b + q ≠ d + wq := by
      intro q hq
      exact Ne.symm (hdisj wq q (by omega) hq)
    have esrcg : ∀ q, q < L → (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) (b + q) = sl.getD q 0 := by
      intro q hq
      rw [up_ne (show b + q ≠ 14 by omega), up_ne (show b + q ≠ 13 by omega),
        up_ne (hdisj2 q hq), up_ne (show b + q ≠ 20 by omega),
        up_ne (show b + q ≠ 16 by omega), up_ne (show b + q ≠ 16 by omega),
        up_ne (show b + q ≠ 21 by omega)]
      exact hsrc q hq
    -- the seven body steps with inline normalization
    have hsteps : exec prog2 ρ S 199 r (memOf w f)
        = exec prog2 ρ (S - 6) 205 r (memOf w (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1))) := by
      rw [exec_add_step (by omega)
          (show prog2.getD 199 Instr.reject = Instr.add 21 18 13 by rfl),
          show f 18 + f 13 = b + j from by rw [hf18, hf13],
        exec_load_step (by omega)
          (show prog2.getD 200 Instr.reject = Instr.load 16 21 by rfl) fi1,
          up_eq, up_ne (show b + j ≠ 21 by omega), hsrc j hjL,
        exec_add_step (by omega)
          (show prog2.getD 201 Instr.reject = Instr.add 16 16 17 by rfl),
          show (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 + (up (up f 21 (b + j)) 16 (sl.getD j 0)) 17 = sl.getD j 0 + ak from by
            rw [up_eq, up_ne (show (17:Nat) ≠ 16 by omega),
              up_ne (show (17:Nat) ≠ 21 by omega), hf17],
        exec_add_step (by omega)
          (show prog2.getD 202 Instr.reject = Instr.add 20 19 14 by rfl),
          show (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 19 + (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 14 = d + wq from by
            rw [up_ne (show (19:Nat) ≠ 16 by omega),
              up_ne (show (19:Nat) ≠ 16 by omega),
              up_ne (show (19:Nat) ≠ 21 by omega), hf19,
              up_ne (show (14:Nat) ≠ 16 by omega),
              up_ne (show (14:Nat) ≠ 16 by omega),
              up_ne (show (14:Nat) ≠ 21 by omega), hf14],
        exec_store_step (by omega)
          (show prog2.getD 203 Instr.reject = Instr.store 20 16 by rfl) fi4,
          up_eq,
          show (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) 16 = sl.getD j 0 + ak from by
            rw [up_ne (show (16:Nat) ≠ 20 by omega), up_eq],
        exec_add_step (by omega)
          (show prog2.getD 204 Instr.reject = Instr.add 13 13 1 by rfl),
          show (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 + (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 1 = j + 1 from by
            rw [up_ne (show (13:Nat) ≠ d + wq by omega),
              up_ne (show (13:Nat) ≠ 20 by omega),
              up_ne (show (13:Nat) ≠ 16 by omega),
              up_ne (show (13:Nat) ≠ 16 by omega),
              up_ne (show (13:Nat) ≠ 21 by omega), hf13,
              up_ne (show (1:Nat) ≠ d + wq by omega),
              up_ne (show (1:Nat) ≠ 20 by omega),
              up_ne (show (1:Nat) ≠ 16 by omega),
              up_ne (show (1:Nat) ≠ 16 by omega),
              up_ne (show (1:Nat) ≠ 21 by omega), h1]]
      simp only [Nat.sub_sub, Nat.reduceAdd]
    by_cases hnext : j + 1 < L
    · have h140 : (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 13 < (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 11 := by rw [e13g, e11g]; exact hnext
      have hS8 : S - 6 - 1 - 1 = S - 8 := by omega
      rw [hsteps, exec_add_step (by omega)
          (show prog2.getD 205 Instr.reject = Instr.add 14 14 1 by rfl),
          show (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 + (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 1 = wq + 1 from by
            rw [up_ne (show (14:Nat) ≠ 13 by omega),
              up_ne (show (14:Nat) ≠ d + wq by omega),
              up_ne (show (14:Nat) ≠ 20 by omega),
              up_ne (show (14:Nat) ≠ 16 by omega),
              up_ne (show (14:Nat) ≠ 16 by omega),
              up_ne (show (14:Nat) ≠ 21 by omega), hf14,
              up_ne (show (1:Nat) ≠ 13 by omega),
              up_ne (show (1:Nat) ≠ d + wq by omega),
              up_ne (show (1:Nat) ≠ 20 by omega),
              up_ne (show (1:Nat) ≠ 16 by omega),
              up_ne (show (1:Nat) ≠ 16 by omega),
              up_ne (show (1:Nat) ≠ 21 by omega), h1],
          exec_blt_lt_step (by omega)
          (show prog2.getD 206 Instr.reject = Instr.blt 13 11 199 by rfl) fi7
          h140, hS8]
      have hwj2 : wq + 1 = L + (j + 1) := by omega
      have hN2 : L - (j + 1) ≤ N := by omega
      have hS2 : 8 * N + 8 ≤ S - 8 := by omega
      obtain ⟨c2, f2, hc2, hex2, harr2, h122, h132, h142, hfit2, hpres2⟩ :=
        ih L b d ak sl out (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) (j + 1) (wq + 1) (S - 8) r hsL hnext hwj2
          e12g e13g e14g e11g e17g e18g e19g e1g e2g esrcg hvfit htake1 hdrop1
          fi7 hbL hdL h2L hb33 hd33 hdisj hN2 hS2
      refine ⟨8 + c2, f2, by omega, ?_, harr2, h122, h132, h142, hfit2, ?_⟩
      · rw [hex2]
        have hS9 : S - 8 - c2 = S - (8 + c2) := by omega
        rw [hS9]
      have q1 : Pres (MReg d L) f (up f 21 (b + j)) := pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
      have q2 : Pres (MReg d L) (up f 21 (b + j)) (up (up f 21 (b + j)) 16 (sl.getD j 0)) := pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      have q3 : Pres (MReg d L) (up (up f 21 (b + j)) 16 (sl.getD j 0)) (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) := pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      have q4 : Pres (MReg d L) (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) := pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      have q5 : Pres (MReg d L) (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) := pres_up (MReg_dst (by omega) (by omega))
      have q6 : Pres (MReg d L) (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) := pres_up (Or.inr (Or.inl rfl))
      have q7 : Pres (MReg d L) (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) := pres_up (Or.inr (Or.inr (Or.inl rfl)))
      exact pres_trans q1 (pres_trans q2 (pres_trans q3 (pres_trans q4
        (pres_trans q5 (pres_trans q6 (pres_trans q7 hpres2))))))
    · have h140 : ¬ (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 13 < (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) 11 := by rw [e13g, e11g]; omega
      have hrw2 : exec prog2 ρ S 199 r (memOf w f)
          = exec prog2 ρ (S - 8) 207 r (memOf w (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1))) := by
        rw [hsteps,
          exec_add_step (by omega)
            (show prog2.getD 205 Instr.reject = Instr.add 14 14 1 by rfl),
          show (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 + (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 1 = wq + 1 from by
            rw [up_ne (show (14:Nat) ≠ 13 by omega),
              up_ne (show (14:Nat) ≠ d + wq by omega),
              up_ne (show (14:Nat) ≠ 20 by omega),
              up_ne (show (14:Nat) ≠ 16 by omega),
              up_ne (show (14:Nat) ≠ 16 by omega),
              up_ne (show (14:Nat) ≠ 21 by omega), hf14,
              up_ne (show (1:Nat) ≠ 13 by omega),
              up_ne (show (1:Nat) ≠ d + wq by omega),
              up_ne (show (1:Nat) ≠ 20 by omega),
              up_ne (show (1:Nat) ≠ 16 by omega),
              up_ne (show (1:Nat) ≠ 16 by omega),
              up_ne (show (1:Nat) ≠ 21 by omega), h1],
          exec_blt_ge_step (by omega)
            (show prog2.getD 206 Instr.reject = Instr.blt 13 11 199 by rfl) fi7 h140]
        simp only [Nat.sub_sub, Nat.reduceAdd]
      have hfull : arrL (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) d (2 * L) = out := by
        have hq2 : wq + 1 = 2 * L := by omega
        rw [hq2] at htake1
        have hto := takeAll (l := out) (n := 2 * L) (by omega)
        have hla : (arrL (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) d (2 * L)).length = 2 * L := by simp [arrL]
        have hta := takeAll (l := arrL (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) d (2 * L)) (n := 2 * L) (by omega)
        rw [← hta, ← hto, htake1, hq2]
      refine ⟨8, (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)), by omega, hrw2, hfull, e12g, by rw [e13g]; omega,
        by rw [e14g]; omega, fi7, ?_⟩
      have q1 : Pres (MReg d L) f (up f 21 (b + j)) := pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
      have q2 : Pres (MReg d L) (up f 21 (b + j)) (up (up f 21 (b + j)) 16 (sl.getD j 0)) := pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      have q3 : Pres (MReg d L) (up (up f 21 (b + j)) 16 (sl.getD j 0)) (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) := pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      have q4 : Pres (MReg d L) (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) := pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      have q5 : Pres (MReg d L) (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) := pres_up (MReg_dst (by omega) (by omega))
      have q6 : Pres (MReg d L) (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) := pres_up (Or.inr (Or.inl rfl))
      have q7 : Pres (MReg d L) (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) (up (up (up (up (up (up (up f 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) := pres_up (Or.inr (Or.inr (Or.inl rfl)))
      exact pres_trans q1 (pres_trans q2 (pres_trans q3 (pres_trans q4
        (pres_trans q5 (pres_trans q6 (pres_up (Or.inr (Or.inr (Or.inl rfl)))))))))

/-! ## §5. The merge loop (pc 103 → 141). -/
/-- Merge loop: both-sides iterations until one side exhausts, then the
matching drain finishes the array.  `wq = i + j` throughout; each
both-sides step is 14 instructions, consuming `mmerge_stepL/J` for the
take/drop invariants. -/
theorem merge2_exec {w : Nat} (ρ : Nat → BitVec w) :
    ∀ (N L b d ak : Nat) (sl out : List Nat) (f : Nat → Nat) (i j wq S r : Nat),
    sl.length = L →
    i ≤ L → j ≤ L → wq = i + j → f 12 = i → f 13 = j → f 14 = wq → f 11 = L →
    f 17 = ak → f 18 = b → f 19 = d → f 1 = 1 → f 2 = 0 →
    (∀ q, q < L → f (b + q) = sl.getD q 0) →
    (∀ v ∈ sl, v + ak < 2 ^ w) →
    (out.take wq = (arrL f d (2 * L)).take wq) →
    (out.drop wq = mmerge (sl.drop i) ((sl.map (fun z => z + ak)).drop j)) →
    out = mmerge sl (sl.map (fun z => z + ak)) →
    (∀ q, f q < 2 ^ w) → b + L < 2 ^ w → d + 2 * L < 2 ^ w → 2 * L < 2 ^ w →
    33 ≤ b → 33 ≤ d → (∀ p q, p < 2 * L → q < L → d + p ≠ b + q) →
    (L - i) + (L - j) ≤ N → 22 * N + 12 ≤ S →
    ∃ c f', c ≤ 22 * N + 12 ∧
      exec prog2 ρ S 169 r (memOf w f) = exec prog2 ρ (S - c) 207 r (memOf w f') ∧
      arrL f' d (2 * L) = out ∧ f' 12 = L ∧ f' 14 = 2 * L ∧
      (∀ q, f' q < 2 ^ w) ∧ Pres (MReg d L) f f' := by
  intro N
  induction N with
  | zero =>
    intro L b d ak sl out f i j wq S r hsL hiLe hjLe hwq hf12 hf13 hf14 hf11 hf17 hf18 hf19 h1 h2 hsrc hvfit htake hdrop hout hfit hbL hdL h2L hb33 hd33 hdisj hfuel hhor
    have hiL : i = L := by omega
    have hjL : j = L := by omega
    have hw2 : wq = 2 * L := by omega
    have hlen : out.length = 2 * L := by
      rw [hout, mmerge_length, List.length_map, hsL]
      omega
    have hfull : arrL f d (2 * L) = out := by
      rw [hw2] at htake
      have hto := takeAll (l := out) (n := 2 * L) (by omega)
      have hla : (arrL f d (2 * L)).length = 2 * L := by simp [arrL]
      have hta := takeAll (l := arrL f d (2 * L)) (n := 2 * L) (by omega)
      rw [← hta, ← hto, htake]
    refine ⟨4, f, by omega, ?_, hfull, by omega, by omega, hfit, ?_⟩
    · rw [exec_blt_ge_step (by omega)
          (show prog2.getD 169 Instr.reject = Instr.blt 13 11 171 by rfl) hfit
          (by rw [hf13, hf11]; omega),
        exec_blt_lt_step (by omega)
          (show prog2.getD 170 Instr.reject = Instr.blt 2 1 189 by rfl) hfit
          (by rw [h2, h1]; omega),
        exec_blt_ge_step (by omega)
          (show prog2.getD 189 Instr.reject = Instr.blt 12 11 191 by rfl) hfit
          (by rw [hf12, hf11]; omega),
        exec_blt_lt_step (by omega)
          (show prog2.getD 190 Instr.reject = Instr.blt 2 1 207 by rfl) hfit
          (by rw [h2, h1]; omega)]
      simp only [Nat.sub_sub, Nat.reduceAdd]
    · intro x hx
      rfl
  | succ N ih =>
    intro L b d ak sl out f i j wq S r hsL hiLe hjLe hwq hf12 hf13 hf14 hf11 hf17 hf18 hf19 h1 h2 hsrc hvfit htake hdrop hout hfit hbL hdL h2L hb33 hd33 hdisj hfuel hhor
    have hMlen : (sl.map (fun z => z + ak)).length = L := by simp [List.length_map, hsL]
    by_cases hj : j < L
    · by_cases hi : i < L
      ·         -- both-sides merge iteration
        have hjl : j < sl.length := by omega
        have fi1 : ∀ q, (up f 20 (b + i)) q < 2 ^ w := up_fit hfit (by have := hbL; omega)
        have fi2 : ∀ q, (up (up f 20 (b + i)) 15 (sl.getD i 0)) q < 2 ^ w := up_fit fi1 (by have := hvfit _ (mem_getD (i := i) (by omega)); omega)
        have fi3 : ∀ q, (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) q < 2 ^ w := up_fit fi2 (by have := hbL; omega)
        have fi4 : ∀ q, (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) q < 2 ^ w := up_fit fi3 (by have := hvfit _ (mem_getD (i := j) (by omega)); omega)
        have hvj : sl.getD j 0 + ak < 2 ^ w := hvfit _ (mem_getD (i := j) (by omega))
        have fi5 : ∀ q, (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) q < 2 ^ w := up_fit fi4 hvj
        have fi6 : ∀ q, (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) q < 2 ^ w := up_fit fi5 (by have := hdL; omega)
        have fi7 : ∀ q, (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) q < 2 ^ w := up_fit fi6 hvj
        have fi8 : ∀ q, (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) q < 2 ^ w := up_fit fi7 (by have := h2L; omega)
        have fi9 : ∀ q, (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) q < 2 ^ w := up_fit fi8 (by have := h2L; omega)
        have hvi : sl.getD i 0 < 2 ^ w := by have := hvfit _ (mem_getD (i := i) (by omega)); omega
        have fi7U : ∀ q, (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) q < 2 ^ w := up_fit fi6 hvi
        have fi8U : ∀ q, (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) q < 2 ^ w := up_fit fi7U (by have := h2L; omega)
        have fi9U : ∀ q, (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) q < 2 ^ w := up_fit fi8U (by have := h2L; omega)
        have e15_5 : up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak) 15 = sl.getD i 0 := by
          rw [up_ne (show (15:Nat) ≠ (16 : Nat) by omega), up_ne (show (15:Nat) ≠ (16 : Nat) by omega), up_ne (show (15:Nat) ≠ (21 : Nat) by omega), up_eq]
        have e16_5 : up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak) 16 = sl.getD j 0 + ak := up_eq _ _ _
        have hlen : out.length = 2 * L := by
          rw [hout, mmerge_length, List.length_map, hsL]
          omega
        have hwqo : wq < out.length := by rw [hlen]; omega
        have hwq2L : wq < 2 * L := by omega
        have hB : (mmerge sl (sl.map (fun z => z + ak))).drop (i + j)
            = mmerge (sl.drop i) ((sl.map (fun z => z + ak)).drop j) := by
          rw [← hwq, ← hout]
          exact hdrop
        by_cases hcmp : sl.getD j 0 + ak < sl.getD i 0
        · -- LTAKEJ
          have hcmpJ : (sl.map (fun z => z + ak)).getD j 0 < sl.getD i 0 := by
            rw [getD_map_add sl ak j hjl]
            exact hcmp
          have hstep := mmerge_stepJ sl (sl.map (fun z => z + ak)) i j
              (by omega) (by omega) hcmpJ hB
          have houtwq : out.getD wq 0 = sl.getD j 0 + ak := by
            rw [hout, hwq, hstep.1, getD_map_add sl ak j hjl]
          have hdrop1 : out.drop (wq + 1)
              = mmerge (sl.drop i) ((sl.map (fun z => z + ak)).drop (j + 1)) := by
            rw [hout, show wq + 1 = i + j + 1 from by omega, hstep.2]
          have hA9 : arrL (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) d (2 * L) = arrL (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) d (2 * L) := by
            rw [show arrL (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) d (2 * L) = arrL (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) d (2 * L) from arrL_up_out (fun q _ => show (14:Nat) ≠ d + q by omega), show arrL (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) d (2 * L) = arrL (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) d (2 * L) from arrL_up_out (fun q _ => show (13:Nat) ≠ d + q by omega)]
          have hA6 : arrL (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) d (2 * L) = arrL f d (2 * L) := by
            rw [show arrL (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) d (2 * L) = arrL (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) d (2 * L) from arrL_up_out (fun q _ => show (20:Nat) ≠ d + q by omega), show arrL (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) d (2 * L) = arrL (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) d (2 * L) from arrL_up_out (fun q _ => show (16:Nat) ≠ d + q by omega), show arrL (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) d (2 * L) = arrL (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) d (2 * L) from arrL_up_out (fun q _ => show (16:Nat) ≠ d + q by omega), show arrL (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) d (2 * L) = arrL (up (up f 20 (b + i)) 15 (sl.getD i 0)) d (2 * L) from arrL_up_out (fun q _ => show (21:Nat) ≠ d + q by omega), show arrL (up (up f 20 (b + i)) 15 (sl.getD i 0)) d (2 * L) = arrL (up f 20 (b + i)) d (2 * L) from arrL_up_out (fun q _ => show (15:Nat) ≠ d + q by omega), show arrL (up f 20 (b + i)) d (2 * L) = arrL (f) d (2 * L) from arrL_up_out (fun q _ => show (20:Nat) ≠ d + q by omega)]
          have htake1 : out.take (wq + 1) = (arrL (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) d (2 * L)).take (wq + 1) := by
            rw [hA9, arrL_take_up hwq2L, hA6, ← htake, takeSucc hwqo, houtwq]
          have e1_8 : up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1) 1 = 1 := by
            rw [up_ne (show (1:Nat) ≠ (13 : Nat) by omega), up_ne (show (1:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (21 : Nat) by omega), up_ne (show (1:Nat) ≠ (15 : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), h1]
          have e2_8 : up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1) 2 = 0 := by
            rw [up_ne (show (2:Nat) ≠ (13 : Nat) by omega), up_ne (show (2:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (2:Nat) ≠ (20 : Nat) by omega), up_ne (show (2:Nat) ≠ (16 : Nat) by omega), up_ne (show (2:Nat) ≠ (16 : Nat) by omega), up_ne (show (2:Nat) ≠ (21 : Nat) by omega), up_ne (show (2:Nat) ≠ (15 : Nat) by omega), up_ne (show (2:Nat) ≠ (20 : Nat) by omega), h2]
          have e12_9 : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1) 12 = i := by
            rw [up_ne (show (12:Nat) ≠ (14 : Nat) by omega), up_ne (show (12:Nat) ≠ (13 : Nat) by omega), up_ne (show (12:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (12:Nat) ≠ (20 : Nat) by omega), up_ne (show (12:Nat) ≠ (16 : Nat) by omega), up_ne (show (12:Nat) ≠ (16 : Nat) by omega), up_ne (show (12:Nat) ≠ (21 : Nat) by omega), up_ne (show (12:Nat) ≠ (15 : Nat) by omega), up_ne (show (12:Nat) ≠ (20 : Nat) by omega), hf12]
          have e13_9 : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1) 13 = j + 1 := by
            rw [up_ne (show (13:Nat) ≠ (14 : Nat) by omega), up_eq]
          have e14_9 : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1) 14 = wq + 1 := by
            rw [up_eq]
          have e11_9 : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1) 11 = L := by
            rw [up_ne (show (11:Nat) ≠ (14 : Nat) by omega), up_ne (show (11:Nat) ≠ (13 : Nat) by omega), up_ne (show (11:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (11:Nat) ≠ (20 : Nat) by omega), up_ne (show (11:Nat) ≠ (16 : Nat) by omega), up_ne (show (11:Nat) ≠ (16 : Nat) by omega), up_ne (show (11:Nat) ≠ (21 : Nat) by omega), up_ne (show (11:Nat) ≠ (15 : Nat) by omega), up_ne (show (11:Nat) ≠ (20 : Nat) by omega), hf11]
          have e17_9 : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1) 17 = ak := by
            rw [up_ne (show (17:Nat) ≠ (14 : Nat) by omega), up_ne (show (17:Nat) ≠ (13 : Nat) by omega), up_ne (show (17:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (17:Nat) ≠ (20 : Nat) by omega), up_ne (show (17:Nat) ≠ (16 : Nat) by omega), up_ne (show (17:Nat) ≠ (16 : Nat) by omega), up_ne (show (17:Nat) ≠ (21 : Nat) by omega), up_ne (show (17:Nat) ≠ (15 : Nat) by omega), up_ne (show (17:Nat) ≠ (20 : Nat) by omega), hf17]
          have e18_9 : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1) 18 = b := by
            rw [up_ne (show (18:Nat) ≠ (14 : Nat) by omega), up_ne (show (18:Nat) ≠ (13 : Nat) by omega), up_ne (show (18:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (18:Nat) ≠ (20 : Nat) by omega), up_ne (show (18:Nat) ≠ (16 : Nat) by omega), up_ne (show (18:Nat) ≠ (16 : Nat) by omega), up_ne (show (18:Nat) ≠ (21 : Nat) by omega), up_ne (show (18:Nat) ≠ (15 : Nat) by omega), up_ne (show (18:Nat) ≠ (20 : Nat) by omega), hf18]
          have e19_9 : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1) 19 = d := by
            rw [up_ne (show (19:Nat) ≠ (14 : Nat) by omega), up_ne (show (19:Nat) ≠ (13 : Nat) by omega), up_ne (show (19:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (19:Nat) ≠ (20 : Nat) by omega), up_ne (show (19:Nat) ≠ (16 : Nat) by omega), up_ne (show (19:Nat) ≠ (16 : Nat) by omega), up_ne (show (19:Nat) ≠ (21 : Nat) by omega), up_ne (show (19:Nat) ≠ (15 : Nat) by omega), up_ne (show (19:Nat) ≠ (20 : Nat) by omega), hf19]
          have e1_9 : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1) 1 = 1 := by
            rw [up_ne (show (1:Nat) ≠ (14 : Nat) by omega), up_ne (show (1:Nat) ≠ (13 : Nat) by omega), up_ne (show (1:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (21 : Nat) by omega), up_ne (show (1:Nat) ≠ (15 : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), h1]
          have e2_9 : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1) 2 = 0 := by
            rw [up_ne (show (2:Nat) ≠ (14 : Nat) by omega), up_ne (show (2:Nat) ≠ (13 : Nat) by omega), up_ne (show (2:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (2:Nat) ≠ (20 : Nat) by omega), up_ne (show (2:Nat) ≠ (16 : Nat) by omega), up_ne (show (2:Nat) ≠ (16 : Nat) by omega), up_ne (show (2:Nat) ≠ (21 : Nat) by omega), up_ne (show (2:Nat) ≠ (15 : Nat) by omega), up_ne (show (2:Nat) ≠ (20 : Nat) by omega), h2]
          have esrc_9 : ∀ q, q < L → up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1) (b + q) = sl.getD q 0 := by
            intro q hq
            rw [up_ne (show b + q ≠ (14 : Nat) by omega), up_ne (show b + q ≠ (13 : Nat) by omega), up_ne (Ne.symm (hdisj wq q (by omega) hq)), up_ne (show b + q ≠ (20 : Nat) by omega), up_ne (show b + q ≠ (16 : Nat) by omega), up_ne (show b + q ≠ (16 : Nat) by omega), up_ne (show b + q ≠ (21 : Nat) by omega), up_ne (show b + q ≠ (15 : Nat) by omega), up_ne (show b + q ≠ (20 : Nat) by omega)]
            exact hsrc q hq
          have hwalk : exec prog2 ρ S 169 r (memOf w f)
              = exec prog2 ρ (S - 14) 169 r (memOf w (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1))) := by
            rw [exec_blt_lt_step (by omega) (show prog2.getD 169 Instr.reject = Instr.blt 13 11 171 by rfl) hfit (by rw [hf13, hf11]; exact hj),
              exec_blt_lt_step (by omega) (show prog2.getD 171 Instr.reject = Instr.blt 12 11 173 by rfl) hfit (by rw [hf12, hf11]; exact hi),
              exec_add_step (by omega) (show prog2.getD 173 Instr.reject = Instr.add 20 18 12 by rfl), show f 18 + f 12 = b + i from by rw [hf18, hf12],
              exec_load_step (by omega) (show prog2.getD 174 Instr.reject = Instr.load 15 20 by rfl) fi1, up_eq, up_ne (show b + i ≠ 20 by omega), hsrc i hi,
              exec_add_step (by omega) (show prog2.getD 175 Instr.reject = Instr.add 21 18 13 by rfl), show up (up f 20 (b + i)) 15 (sl.getD i 0) 18 + up (up f 20 (b + i)) 15 (sl.getD i 0) 13 = b + j from by rw [up_ne (show (18:Nat) ≠ (15 : Nat) by omega), up_ne (show (18:Nat) ≠ (20 : Nat) by omega), hf18, up_ne (show (13:Nat) ≠ (15 : Nat) by omega), up_ne (show (13:Nat) ≠ (20 : Nat) by omega), hf13],
              exec_load_step (by omega) (show prog2.getD 176 Instr.reject = Instr.load 16 21 by rfl) fi3, up_eq, up_ne (show b + j ≠ 21 by omega), up_ne (show b + j ≠ (15 : Nat) by omega), up_ne (show b + j ≠ (20 : Nat) by omega), hsrc j hj,
              exec_add_step (by omega) (show prog2.getD 177 Instr.reject = Instr.add 16 16 17 by rfl), show up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0) 16 + up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0) 17 = sl.getD j 0 + ak from by rw [up_eq, up_ne (show (17:Nat) ≠ (16 : Nat) by omega), up_ne (show (17:Nat) ≠ (21 : Nat) by omega), up_ne (show (17:Nat) ≠ (15 : Nat) by omega), up_ne (show (17:Nat) ≠ (20 : Nat) by omega), hf17],
              exec_blt_lt_step (by omega) (show prog2.getD 178 Instr.reject = Instr.blt 16 15 180 by rfl) fi5 (by rw [e16_5, e15_5]; exact hcmp),
              exec_add_step (by omega) (show prog2.getD 180 Instr.reject = Instr.add 20 19 14 by rfl), show up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak) 19 + up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak) 14 = d + wq from by rw [up_ne (show (19:Nat) ≠ (16 : Nat) by omega), up_ne (show (19:Nat) ≠ (16 : Nat) by omega), up_ne (show (19:Nat) ≠ (21 : Nat) by omega), up_ne (show (19:Nat) ≠ (15 : Nat) by omega), up_ne (show (19:Nat) ≠ (20 : Nat) by omega), hf19, up_ne (show (14:Nat) ≠ (16 : Nat) by omega), up_ne (show (14:Nat) ≠ (16 : Nat) by omega), up_ne (show (14:Nat) ≠ (21 : Nat) by omega), up_ne (show (14:Nat) ≠ (15 : Nat) by omega), up_ne (show (14:Nat) ≠ (20 : Nat) by omega), hf14],
              exec_store_step (by omega) (show prog2.getD 181 Instr.reject = Instr.store 20 16 by rfl) fi6, up_eq, up_ne (show (16:Nat) ≠ 20 by omega), up_eq,
              exec_add_step (by omega) (show prog2.getD 182 Instr.reject = Instr.add 13 13 1 by rfl), show up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak) 13 + up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak) 1 = j + 1 from by rw [up_ne (show (13:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (13:Nat) ≠ (20 : Nat) by omega), up_ne (show (13:Nat) ≠ (16 : Nat) by omega), up_ne (show (13:Nat) ≠ (16 : Nat) by omega), up_ne (show (13:Nat) ≠ (21 : Nat) by omega), up_ne (show (13:Nat) ≠ (15 : Nat) by omega), up_ne (show (13:Nat) ≠ (20 : Nat) by omega), hf13, up_ne (show (1:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (21 : Nat) by omega), up_ne (show (1:Nat) ≠ (15 : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), h1],
              exec_blt_lt_step (by omega) (show prog2.getD 183 Instr.reject = Instr.blt 2 1 187 by rfl) fi8 (by rw [e2_8, e1_8]; omega),
              exec_add_step (by omega) (show prog2.getD 187 Instr.reject = Instr.add 14 14 1 by rfl), show up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1) 14 + up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1) 1 = wq + 1 from by rw [up_ne (show (14:Nat) ≠ (13 : Nat) by omega), up_ne (show (14:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (14:Nat) ≠ (20 : Nat) by omega), up_ne (show (14:Nat) ≠ (16 : Nat) by omega), up_ne (show (14:Nat) ≠ (16 : Nat) by omega), up_ne (show (14:Nat) ≠ (21 : Nat) by omega), up_ne (show (14:Nat) ≠ (15 : Nat) by omega), up_ne (show (14:Nat) ≠ (20 : Nat) by omega), hf14, up_ne (show (1:Nat) ≠ (13 : Nat) by omega), up_ne (show (1:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (21 : Nat) by omega), up_ne (show (1:Nat) ≠ (15 : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), h1],
              exec_blt_lt_step (by omega) (show prog2.getD 188 Instr.reject = Instr.blt 2 1 169 by rfl) fi9 (by rw [e2_9, e1_9]; omega)]
            simp only [Nat.sub_sub, Nat.reduceAdd]
          obtain ⟨c2, f2, hc2, hex2, harr2, h122, h142, hfit2, hpres2⟩ :=
            ih L b d ak sl out (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD j 0 + ak)) 13 (j + 1)) 14 (wq + 1)) i (j + 1) (wq + 1) (S - 14) r hsL
              (by omega) (by omega) (by omega)
              e12_9 e13_9 e14_9 e11_9 e17_9 e18_9 e19_9 e1_9 e2_9 esrc_9
              hvfit htake1 hdrop1 hout fi9 hbL hdL h2L hb33 hd33 hdisj
              (by omega) (by omega)
          refine ⟨14 + c2, f2, by omega, ?_, harr2, h122, h142, hfit2, ?_⟩
          · rw [hwalk, hex2]
            have hS14 : S - 14 - c2 = S - (14 + c2) := by omega
            rw [hS14]
          · exact pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (pres_trans (pres_up (MReg_dst (by omega) (by omega))) (pres_trans (pres_up (Or.inr (Or.inl rfl))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inl rfl)))) (hpres2)))))))))
        · -- LTAKEL
          have hcmpL : ¬ (sl.map (fun z => z + ak)).getD j 0 < sl.getD i 0 := by
            rw [getD_map_add sl ak j hjl]
            exact hcmp
          have hstep := mmerge_stepL sl (sl.map (fun z => z + ak)) i j
              (by omega) (by omega) hcmpL hB
          have houtwq : out.getD wq 0 = sl.getD i 0 := by
            rw [hout, hwq, hstep.1]
          have hdrop1 : out.drop (wq + 1)
              = mmerge (sl.drop (i + 1)) ((sl.map (fun z => z + ak)).drop j) := by
            rw [hout, show wq + 1 = i + j + 1 from by omega, hstep.2]
          have hA9 : arrL (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) d (2 * L) = arrL (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) d (2 * L) := by
            rw [show arrL (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) d (2 * L) = arrL (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) d (2 * L) from arrL_up_out (fun q _ => show (14:Nat) ≠ d + q by omega), show arrL (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) d (2 * L) = arrL (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) d (2 * L) from arrL_up_out (fun q _ => show (12:Nat) ≠ d + q by omega)]
          have hA6 : arrL (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) d (2 * L) = arrL f d (2 * L) := by
            rw [show arrL (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) d (2 * L) = arrL (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) d (2 * L) from arrL_up_out (fun q _ => show (20:Nat) ≠ d + q by omega), show arrL (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) d (2 * L) = arrL (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) d (2 * L) from arrL_up_out (fun q _ => show (16:Nat) ≠ d + q by omega), show arrL (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) d (2 * L) = arrL (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) d (2 * L) from arrL_up_out (fun q _ => show (16:Nat) ≠ d + q by omega), show arrL (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) d (2 * L) = arrL (up (up f 20 (b + i)) 15 (sl.getD i 0)) d (2 * L) from arrL_up_out (fun q _ => show (21:Nat) ≠ d + q by omega), show arrL (up (up f 20 (b + i)) 15 (sl.getD i 0)) d (2 * L) = arrL (up f 20 (b + i)) d (2 * L) from arrL_up_out (fun q _ => show (15:Nat) ≠ d + q by omega), show arrL (up f 20 (b + i)) d (2 * L) = arrL (f) d (2 * L) from arrL_up_out (fun q _ => show (20:Nat) ≠ d + q by omega)]
          have htake1 : out.take (wq + 1) = (arrL (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) d (2 * L)).take (wq + 1) := by
            rw [hA9, arrL_take_up hwq2L, hA6, ← htake, takeSucc hwqo, houtwq]
          have e1_5 : up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak) 1 = 1 := by
            rw [up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (21 : Nat) by omega), up_ne (show (1:Nat) ≠ (15 : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), h1]
          have e2_5 : up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak) 2 = 0 := by
            rw [up_ne (show (2:Nat) ≠ (16 : Nat) by omega), up_ne (show (2:Nat) ≠ (16 : Nat) by omega), up_ne (show (2:Nat) ≠ (21 : Nat) by omega), up_ne (show (2:Nat) ≠ (15 : Nat) by omega), up_ne (show (2:Nat) ≠ (20 : Nat) by omega), h2]
          have e12_9U : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1) 12 = i + 1 := by
            rw [up_ne (show (12:Nat) ≠ (14 : Nat) by omega), up_eq]
          have e13_9U : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1) 13 = j := by
            rw [up_ne (show (13:Nat) ≠ (14 : Nat) by omega), up_ne (show (13:Nat) ≠ (12 : Nat) by omega), up_ne (show (13:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (13:Nat) ≠ (20 : Nat) by omega), up_ne (show (13:Nat) ≠ (16 : Nat) by omega), up_ne (show (13:Nat) ≠ (16 : Nat) by omega), up_ne (show (13:Nat) ≠ (21 : Nat) by omega), up_ne (show (13:Nat) ≠ (15 : Nat) by omega), up_ne (show (13:Nat) ≠ (20 : Nat) by omega), hf13]
          have e14_9U : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1) 14 = wq + 1 := by
            rw [up_eq]
          have e11_9U : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1) 11 = L := by
            rw [up_ne (show (11:Nat) ≠ (14 : Nat) by omega), up_ne (show (11:Nat) ≠ (12 : Nat) by omega), up_ne (show (11:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (11:Nat) ≠ (20 : Nat) by omega), up_ne (show (11:Nat) ≠ (16 : Nat) by omega), up_ne (show (11:Nat) ≠ (16 : Nat) by omega), up_ne (show (11:Nat) ≠ (21 : Nat) by omega), up_ne (show (11:Nat) ≠ (15 : Nat) by omega), up_ne (show (11:Nat) ≠ (20 : Nat) by omega), hf11]
          have e17_9U : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1) 17 = ak := by
            rw [up_ne (show (17:Nat) ≠ (14 : Nat) by omega), up_ne (show (17:Nat) ≠ (12 : Nat) by omega), up_ne (show (17:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (17:Nat) ≠ (20 : Nat) by omega), up_ne (show (17:Nat) ≠ (16 : Nat) by omega), up_ne (show (17:Nat) ≠ (16 : Nat) by omega), up_ne (show (17:Nat) ≠ (21 : Nat) by omega), up_ne (show (17:Nat) ≠ (15 : Nat) by omega), up_ne (show (17:Nat) ≠ (20 : Nat) by omega), hf17]
          have e18_9U : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1) 18 = b := by
            rw [up_ne (show (18:Nat) ≠ (14 : Nat) by omega), up_ne (show (18:Nat) ≠ (12 : Nat) by omega), up_ne (show (18:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (18:Nat) ≠ (20 : Nat) by omega), up_ne (show (18:Nat) ≠ (16 : Nat) by omega), up_ne (show (18:Nat) ≠ (16 : Nat) by omega), up_ne (show (18:Nat) ≠ (21 : Nat) by omega), up_ne (show (18:Nat) ≠ (15 : Nat) by omega), up_ne (show (18:Nat) ≠ (20 : Nat) by omega), hf18]
          have e19_9U : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1) 19 = d := by
            rw [up_ne (show (19:Nat) ≠ (14 : Nat) by omega), up_ne (show (19:Nat) ≠ (12 : Nat) by omega), up_ne (show (19:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (19:Nat) ≠ (20 : Nat) by omega), up_ne (show (19:Nat) ≠ (16 : Nat) by omega), up_ne (show (19:Nat) ≠ (16 : Nat) by omega), up_ne (show (19:Nat) ≠ (21 : Nat) by omega), up_ne (show (19:Nat) ≠ (15 : Nat) by omega), up_ne (show (19:Nat) ≠ (20 : Nat) by omega), hf19]
          have e1_9U : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1) 1 = 1 := by
            rw [up_ne (show (1:Nat) ≠ (14 : Nat) by omega), up_ne (show (1:Nat) ≠ (12 : Nat) by omega), up_ne (show (1:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (21 : Nat) by omega), up_ne (show (1:Nat) ≠ (15 : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), h1]
          have e2_9U : up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1) 2 = 0 := by
            rw [up_ne (show (2:Nat) ≠ (14 : Nat) by omega), up_ne (show (2:Nat) ≠ (12 : Nat) by omega), up_ne (show (2:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (2:Nat) ≠ (20 : Nat) by omega), up_ne (show (2:Nat) ≠ (16 : Nat) by omega), up_ne (show (2:Nat) ≠ (16 : Nat) by omega), up_ne (show (2:Nat) ≠ (21 : Nat) by omega), up_ne (show (2:Nat) ≠ (15 : Nat) by omega), up_ne (show (2:Nat) ≠ (20 : Nat) by omega), h2]
          have esrc_9U : ∀ q, q < L → up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1) (b + q) = sl.getD q 0 := by
            intro q hq
            rw [up_ne (show b + q ≠ (14 : Nat) by omega), up_ne (show b + q ≠ (12 : Nat) by omega), up_ne (Ne.symm (hdisj wq q (by omega) hq)), up_ne (show b + q ≠ (20 : Nat) by omega), up_ne (show b + q ≠ (16 : Nat) by omega), up_ne (show b + q ≠ (16 : Nat) by omega), up_ne (show b + q ≠ (21 : Nat) by omega), up_ne (show b + q ≠ (15 : Nat) by omega), up_ne (show b + q ≠ (20 : Nat) by omega)]
            exact hsrc q hq
          have hwalk : exec prog2 ρ S 169 r (memOf w f)
              = exec prog2 ρ (S - 14) 169 r (memOf w (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1))) := by
            rw [exec_blt_lt_step (by omega) (show prog2.getD 169 Instr.reject = Instr.blt 13 11 171 by rfl) hfit (by rw [hf13, hf11]; exact hj),
              exec_blt_lt_step (by omega) (show prog2.getD 171 Instr.reject = Instr.blt 12 11 173 by rfl) hfit (by rw [hf12, hf11]; exact hi),
              exec_add_step (by omega) (show prog2.getD 173 Instr.reject = Instr.add 20 18 12 by rfl), show f 18 + f 12 = b + i from by rw [hf18, hf12],
              exec_load_step (by omega) (show prog2.getD 174 Instr.reject = Instr.load 15 20 by rfl) fi1, up_eq, up_ne (show b + i ≠ 20 by omega), hsrc i hi,
              exec_add_step (by omega) (show prog2.getD 175 Instr.reject = Instr.add 21 18 13 by rfl), show up (up f 20 (b + i)) 15 (sl.getD i 0) 18 + up (up f 20 (b + i)) 15 (sl.getD i 0) 13 = b + j from by rw [up_ne (show (18:Nat) ≠ (15 : Nat) by omega), up_ne (show (18:Nat) ≠ (20 : Nat) by omega), hf18, up_ne (show (13:Nat) ≠ (15 : Nat) by omega), up_ne (show (13:Nat) ≠ (20 : Nat) by omega), hf13],
              exec_load_step (by omega) (show prog2.getD 176 Instr.reject = Instr.load 16 21 by rfl) fi3, up_eq, up_ne (show b + j ≠ 21 by omega), up_ne (show b + j ≠ (15 : Nat) by omega), up_ne (show b + j ≠ (20 : Nat) by omega), hsrc j hj,
              exec_add_step (by omega) (show prog2.getD 177 Instr.reject = Instr.add 16 16 17 by rfl), show up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0) 16 + up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0) 17 = sl.getD j 0 + ak from by rw [up_eq, up_ne (show (17:Nat) ≠ (16 : Nat) by omega), up_ne (show (17:Nat) ≠ (21 : Nat) by omega), up_ne (show (17:Nat) ≠ (15 : Nat) by omega), up_ne (show (17:Nat) ≠ (20 : Nat) by omega), hf17],
              exec_blt_ge_step (by omega) (show prog2.getD 178 Instr.reject = Instr.blt 16 15 180 by rfl) fi5 (by rw [e16_5, e15_5]; exact hcmp),
              exec_blt_lt_step (by omega) (show prog2.getD 179 Instr.reject = Instr.blt 2 1 184 by rfl) fi5 (by rw [e2_5, e1_5]; omega),
              exec_add_step (by omega) (show prog2.getD 184 Instr.reject = Instr.add 20 19 14 by rfl), show up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak) 19 + up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak) 14 = d + wq from by rw [up_ne (show (19:Nat) ≠ (16 : Nat) by omega), up_ne (show (19:Nat) ≠ (16 : Nat) by omega), up_ne (show (19:Nat) ≠ (21 : Nat) by omega), up_ne (show (19:Nat) ≠ (15 : Nat) by omega), up_ne (show (19:Nat) ≠ (20 : Nat) by omega), hf19, up_ne (show (14:Nat) ≠ (16 : Nat) by omega), up_ne (show (14:Nat) ≠ (16 : Nat) by omega), up_ne (show (14:Nat) ≠ (21 : Nat) by omega), up_ne (show (14:Nat) ≠ (15 : Nat) by omega), up_ne (show (14:Nat) ≠ (20 : Nat) by omega), hf14],
              exec_store_step (by omega) (show prog2.getD 185 Instr.reject = Instr.store 20 15 by rfl) fi6, up_eq, up_ne (show (15:Nat) ≠ 20 by omega), e15_5,
              exec_add_step (by omega) (show prog2.getD 186 Instr.reject = Instr.add 12 12 1 by rfl), show up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0) 12 + up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0) 1 = i + 1 from by rw [up_ne (show (12:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (12:Nat) ≠ (20 : Nat) by omega), up_ne (show (12:Nat) ≠ (16 : Nat) by omega), up_ne (show (12:Nat) ≠ (16 : Nat) by omega), up_ne (show (12:Nat) ≠ (21 : Nat) by omega), up_ne (show (12:Nat) ≠ (15 : Nat) by omega), up_ne (show (12:Nat) ≠ (20 : Nat) by omega), hf12, up_ne (show (1:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (21 : Nat) by omega), up_ne (show (1:Nat) ≠ (15 : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), h1],
              exec_add_step (by omega) (show prog2.getD 187 Instr.reject = Instr.add 14 14 1 by rfl), show up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1) 14 + up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1) 1 = wq + 1 from by rw [up_ne (show (14:Nat) ≠ (12 : Nat) by omega), up_ne (show (14:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (14:Nat) ≠ (20 : Nat) by omega), up_ne (show (14:Nat) ≠ (16 : Nat) by omega), up_ne (show (14:Nat) ≠ (16 : Nat) by omega), up_ne (show (14:Nat) ≠ (21 : Nat) by omega), up_ne (show (14:Nat) ≠ (15 : Nat) by omega), up_ne (show (14:Nat) ≠ (20 : Nat) by omega), hf14, up_ne (show (1:Nat) ≠ (12 : Nat) by omega), up_ne (show (1:Nat) ≠ (d + wq : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (16 : Nat) by omega), up_ne (show (1:Nat) ≠ (21 : Nat) by omega), up_ne (show (1:Nat) ≠ (15 : Nat) by omega), up_ne (show (1:Nat) ≠ (20 : Nat) by omega), h1],
              exec_blt_lt_step (by omega) (show prog2.getD 188 Instr.reject = Instr.blt 2 1 169 by rfl) fi9U (by rw [e2_9U, e1_9U]; omega)]
            simp only [Nat.sub_sub, Nat.reduceAdd]
          obtain ⟨c2, f2, hc2, hex2, harr2, h122, h142, hfit2, hpres2⟩ :=
            ih L b d ak sl out (up (up (up (up (up (up (up (up (up f 20 (b + i)) 15 (sl.getD i 0)) 21 (b + j)) 16 (sl.getD j 0)) 16 (sl.getD j 0 + ak)) 20 (d + wq)) (d + wq) (sl.getD i 0)) 12 (i + 1)) 14 (wq + 1)) (i + 1) j (wq + 1) (S - 14) r hsL
              (by omega) (by omega) (by omega)
              e12_9U e13_9U e14_9U e11_9U e17_9U e18_9U e19_9U e1_9U e2_9U esrc_9U
              hvfit htake1 hdrop1 hout fi9U hbL hdL h2L hb33 hd33 hdisj
              (by omega) (by omega)
          refine ⟨14 + c2, f2, by omega, ?_, harr2, h122, h142, hfit2, ?_⟩
          · rw [hwalk, hex2]
            have hS14 : S - 14 - c2 = S - (14 + c2) := by omega
            rw [hS14]
          · exact pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (pres_trans (pres_up (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (pres_trans (pres_up (MReg_dst (by omega) (by omega))) (pres_trans (pres_up (Or.inl rfl)) (pres_trans (pres_up (Or.inr (Or.inr (Or.inl rfl)))) (hpres2)))))))))
      · have hiL : i = L := by omega
        have hdropDJ : out.drop wq = (sl.map (fun z => z + ak)).drop j := by
          rw [hdrop, hiL, dropNil (by rw [hsL]; exact Nat.le_refl L), mmerge_nil_l]
        have hwalkB : exec prog2 ρ S 169 r (memOf w f)
            = exec prog2 ρ (S - 3) 199 r (memOf w f) := by
          rw [exec_blt_lt_step (by omega)
              (show prog2.getD 169 Instr.reject = Instr.blt 13 11 171 by rfl) hfit
              (by rw [hf13, hf11]; exact hj),
            exec_blt_ge_step (by omega)
              (show prog2.getD 171 Instr.reject = Instr.blt 12 11 173 by rfl) hfit
              (by rw [hf12, hf11, hiL]; omega),
            exec_blt_lt_step (by omega)
              (show prog2.getD 172 Instr.reject = Instr.blt 2 1 199 by rfl) hfit
              (by rw [h2, h1]; omega)]
          simp only [Nat.sub_sub, Nat.reduceAdd]
        obtain ⟨c2, f2, hc2, hex2, harr2, h122, h132, h142, hfit2, hpres2⟩ :=
          djLoop2_exec ρ (L - j) L b d ak sl out f j wq (S - 3) r hsL hj
            (by omega) (by rw [hf12, hiL]) hf13 hf14 hf11 hf17 hf18 hf19 h1 h2
            hsrc hvfit htake hdropDJ hfit hbL hdL h2L hb33 hd33 hdisj
            (Nat.le_refl _) (by omega)
        refine ⟨3 + c2, f2, by omega, ?_, harr2, h122, h142, hfit2, hpres2⟩
        · rw [hwalkB, hex2]
          have hS3 : S - 3 - c2 = S - (3 + c2) := by omega
          rw [hS3]
    · have hjL : j = L := by omega
      by_cases hi2 : i < L
      · have hdropDI : out.drop wq = sl.drop i := by
          have hmd : (sl.map (fun z => z + ak)).drop L = [] := dropNil (by omega)
          rw [hdrop, hjL, hmd, mmerge_nil_r]
        have hvfit0 : ∀ v ∈ sl, v < 2 ^ w := fun v hv => by
          have := hvfit v hv
          omega
        have hwalkA1 : exec prog2 ρ S 169 r (memOf w f)
            = exec prog2 ρ (S - 3) 191 r (memOf w f) := by
          rw [exec_blt_ge_step (by omega)
              (show prog2.getD 169 Instr.reject = Instr.blt 13 11 171 by rfl) hfit
              (by rw [hf13, hf11]; exact hj),
            exec_blt_lt_step (by omega)
              (show prog2.getD 170 Instr.reject = Instr.blt 2 1 189 by rfl) hfit
              (by rw [h2, h1]; omega),
            exec_blt_lt_step (by omega)
              (show prog2.getD 189 Instr.reject = Instr.blt 12 11 191 by rfl) hfit
              (by rw [hf12, hf11]; exact hi2)]
          simp only [Nat.sub_sub, Nat.reduceAdd]
        obtain ⟨c2, f2, hc2, hex2, harr2, h122, h142, hfit2, hpres2⟩ :=
          diLoop2_exec ρ (L - i) L b d sl out f i wq (S - 3) r hsL hi2
            (by omega) hf12 hf14 hf11 hf18 hf19 h1 h2
            hsrc hvfit0 htake hdropDI hfit hbL hdL h2L hb33 hd33 hdisj
            (Nat.le_refl _) (by omega)
        refine ⟨3 + c2, f2, by omega, ?_, harr2, h122, h142, hfit2, hpres2⟩
        · rw [hwalkA1, hex2]
          have hS3 : S - 3 - c2 = S - (3 + c2) := by omega
          rw [hS3]
      · have hw2 : wq = 2 * L := by omega
        have hlen : out.length = 2 * L := by
          rw [hout, mmerge_length, List.length_map, hsL]
          omega
        have hfull : arrL f d (2 * L) = out := by
          rw [hw2] at htake
          have hto := takeAll (l := out) (n := 2 * L) (by omega)
          have hla : (arrL f d (2 * L)).length = 2 * L := by simp [arrL]
          have hta := takeAll (l := arrL f d (2 * L)) (n := 2 * L) (by omega)
          rw [← hta, ← hto, htake]
        refine ⟨4, f, by omega, ?_, hfull, by omega, by omega, hfit, ?_⟩
        · rw [exec_blt_ge_step (by omega)
              (show prog2.getD 169 Instr.reject = Instr.blt 13 11 171 by rfl) hfit
              (by rw [hf13, hf11]; omega),
            exec_blt_lt_step (by omega)
              (show prog2.getD 170 Instr.reject = Instr.blt 2 1 189 by rfl) hfit
              (by rw [h2, h1]; omega),
            exec_blt_ge_step (by omega)
              (show prog2.getD 189 Instr.reject = Instr.blt 12 11 191 by rfl) hfit
              (by rw [hf12, hf11]; omega),
            exec_blt_lt_step (by omega)
              (show prog2.getD 190 Instr.reject = Instr.blt 2 1 207 by rfl) hfit
              (by rw [h2, h1]; omega)]
          simp only [Nat.sub_sub, Nat.reduceAdd]
        · intro x hx
          rfl

/-! ## §5. One round (pc 164 → 213). -/

/--
One full round `k` (1 ≤ k ≤ n - n/2): L2ROUND setup (164–168), the
merge (169–207, via `merge2_exec` from `(0,0,0)`), the L2SWAP tail
(207–212).  Lands at pc 213 with the guard `blt 10 21 164` pending. -/
theorem round2_exec {w n : Nat} (ρ : Nat → BitVec w) {x : Instance n}
    (hn : 3 ≤ n) (hw : wordLength n x.bits ≤ w) :
    ∀ (k L b d : Nat) (f : Nat → Nat) (S r : Nat),
    1 ≤ k → k ≤ n - n / 2 → L = 2 ^ (k - 1) →
    f 1 = 1 → f 2 = 0 → f 7 = n → f 8 = 2 * n + 23 → f 10 = n / 2 + k → f 11 = L → f 18 = b → f 19 = d →
    arrL f b L = halfSums (fun i => instA x (n / 2 + i)) (k - 1) →
    (b = BD2 n ∧ d = BD2 n + 2 ^ (n - n / 2) + 1 ∨
      d = BD2 n ∧ b = BD2 n + 2 ^ (n - n / 2) + 1) →
    (∀ i, 1 ≤ i → i ≤ n - n / 2 →
      f (2 * n + 23 + n / 2 + i) = instA x (n / 2 + (i - 1))) →
    (∀ i, i < n → instA x i < 2 ^ w) →
    (∀ q, f q < 2 ^ w) →
    (∀ c, c ≤ BD2 n + 2 * 2 ^ (n - n / 2) + 1 → c < 2 ^ w) →
    44 * L + 23 ≤ S →
    ∃ c f', c ≤ 44 * L + 23 ∧
      exec prog2 ρ S 164 r (memOf w f) = exec prog2 ρ (S - c) 213 r (memOf w f') ∧
      f' 10 = n / 2 + k + 1 ∧ f' 11 = 2 * L ∧ f' 18 = d ∧ f' 19 = b ∧ f' 21 = n + 1 ∧
      arrL f' d (2 * L) = halfSums (fun i => instA x (n / 2 + i)) k ∧
      f' 1 = 1 ∧ f' 2 = 0 ∧ f' 7 = n ∧ f' 8 = 2 * n + 23 ∧ f' 6 = f 6 ∧ f' 9 = f 9 ∧
      (∀ q, f' q < 2 ^ w) ∧ Pres (AReg2 n) f f' := by
  intro k L b d f S r hk1 hkh hL hf1 hf2 hf7 hf8 hf10 hf11 hf18 hf19
    harr hbases hrel hin hfit haddr hS
  have h2h1 : (1:Nat) ≤ 2 ^ (n - n / 2) := Nat.one_le_two_pow
  have hBD : BD2 n = 3 * n + 25 + 2 * 2 ^ (n / 2) + 2 := rfl
  have h4 : (4:Nat) ≤ 2 ^ (n / 2 + 1) := by
    have h2p : (2:Nat) ^ 2 ≤ 2 ^ (n / 2 + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    rw [show (2:Nat) ^ 2 = 4 from rfl] at h2p
    exact h2p
  rw [hBD] at hbases
  have hbd33 : 33 ≤ b ∧ 33 ≤ d := by
    rcases hbases with ⟨hb, hd⟩|⟨hd, hb⟩ <;> omega
  obtain ⟨hb33, hd33⟩ := hbd33
  have hLh : L ≤ 2 ^ (n - n / 2) := by
    rw [hL]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have h2k : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← Nat.pow_succ', show (k - 1).succ = k from by omega]
  have h2Lh : 2 * L ≤ 2 ^ (n - n / 2) := by
    rw [hL, ← h2k]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have h2p1 : 2 ^ (n - n / 2 + 1) = 2 * 2 ^ (n - n / 2) := by rw [Nat.pow_succ, Nat.mul_comm]
  have hak : instA x (n / 2 + (k - 1)) < 2 ^ w := hin (n / 2 + (k - 1)) (by omega)
  have hfit1 : ∀ q, (up f 20 (2 * n + 23 + n / 2 + k)) q < 2 ^ w :=
    up_fit hfit (haddr _ (by rw [hBD]; omega))
  have hfit2 : ∀ q, (up (up f 20 (2 * n + 23 + n / 2 + k)) 17 (instA x (n / 2 + (k - 1)))) q < 2 ^ w :=
    up_fit hfit1 hak
  have hwalk5 : exec prog2 ρ S 164 r (memOf w f)
      = exec prog2 ρ (S - 5) 169 r (memOf w (up (up (up (up (up f 20 (2 * n + 23 + n / 2 + k)) 17 (instA x (n / 2 + (k - 1)))) 12 0) 13 0) 14 0)) := by
    rw [exec_add_step (by omega) (show prog2.getD 164 Instr.reject = Instr.add 20 8 10 by rfl),
        show f 8 + f 10 = 2 * n + 23 + n / 2 + k from by rw [hf8, hf10]; omega,
        exec_load_step (by omega) (show prog2.getD 165 Instr.reject = Instr.load 17 20 by rfl)
          hfit1,
        up_eq, up_ne (show 2 * n + 23 + n / 2 + k ≠ 20 by omega),
        hrel k (by omega) (by omega),
        subs3_exec hfit2
          (show prog2.getD 166 Instr.reject = Instr.sub 12 12 12 by rfl)
          (show prog2.getD 167 Instr.reject = Instr.sub 13 13 13 by rfl)
          (show prog2.getD 168 Instr.reject = Instr.sub 14 14 14 by rfl)
          (by omega)]
    simp only [Nat.sub_sub, Nat.reduceAdd]
  have g12 : (up (up (up (up (up f 20 (2 * n + 23 + n / 2 + k)) 17 (instA x (n / 2 + (k - 1)))) 12 0) 13 0) 14 0) 12 = 0 := by
    rw [up_ne (show (12:Nat) ≠ 14 by omega), up_ne (show (12:Nat) ≠ 13 by omega), up_eq]
  have g13 : (up (up (up (up (up f 20 (2 * n + 23 + n / 2 + k)) 17 (instA x (n / 2 + (k - 1)))) 12 0) 13 0) 14 0) 13 = 0 := by
    rw [up_ne (show (13:Nat) ≠ 14 by omega), up_eq]
  have g14 : (up (up (up (up (up f 20 (2 * n + 23 + n / 2 + k)) 17 (instA x (n / 2 + (k - 1)))) 12 0) 13 0) 14 0) 14 = 0 := by rw [up_eq]
  have g11 : (up (up (up (up (up f 20 (2 * n + 23 + n / 2 + k)) 17 (instA x (n / 2 + (k - 1)))) 12 0) 13 0) 14 0) 11 = L := by
    rw [up_ne (show (11:Nat) ≠ 14 by omega), up_ne (show (11:Nat) ≠ 13 by omega),
      up_ne (show (11:Nat) ≠ 12 by omega), up_ne (show (11:Nat) ≠ 17 by omega),
      up_ne (show (11:Nat) ≠ 20 by omega), hf11]
  have g17 : (up (up (up (up (up f 20 (2 * n + 23 + n / 2 + k)) 17 (instA x (n / 2 + (k - 1)))) 12 0) 13 0) 14 0) 17 = instA x (n / 2 + (k - 1)) := by
    rw [up_ne (show (17:Nat) ≠ 14 by omega), up_ne (show (17:Nat) ≠ 13 by omega),
      up_ne (show (17:Nat) ≠ 12 by omega), up_eq]
  have g18 : (up (up (up (up (up f 20 (2 * n + 23 + n / 2 + k)) 17 (instA x (n / 2 + (k - 1)))) 12 0) 13 0) 14 0) 18 = b := by
    rw [up_ne (show (18:Nat) ≠ 14 by omega), up_ne (show (18:Nat) ≠ 13 by omega),
      up_ne (show (18:Nat) ≠ 12 by omega), up_ne (show (18:Nat) ≠ 17 by omega),
      up_ne (show (18:Nat) ≠ 20 by omega), hf18]
  have g19 : (up (up (up (up (up f 20 (2 * n + 23 + n / 2 + k)) 17 (instA x (n / 2 + (k - 1)))) 12 0) 13 0) 14 0) 19 = d := by
    rw [up_ne (show (19:Nat) ≠ 14 by omega), up_ne (show (19:Nat) ≠ 13 by omega),
      up_ne (show (19:Nat) ≠ 12 by omega), up_ne (show (19:Nat) ≠ 17 by omega),
      up_ne (show (19:Nat) ≠ 20 by omega), hf19]
  have g1 : (up (up (up (up (up f 20 (2 * n + 23 + n / 2 + k)) 17 (instA x (n / 2 + (k - 1)))) 12 0) 13 0) 14 0) 1 = 1 := by
    rw [up_ne (show (1:Nat) ≠ 14 by omega), up_ne (show (1:Nat) ≠ 13 by omega),
      up_ne (show (1:Nat) ≠ 12 by omega), up_ne (show (1:Nat) ≠ 17 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), hf1]
  have g2 : (up (up (up (up (up f 20 (2 * n + 23 + n / 2 + k)) 17 (instA x (n / 2 + (k - 1)))) 12 0) 13 0) 14 0) 2 = 0 := by
    rw [up_ne (show (2:Nat) ≠ 14 by omega), up_ne (show (2:Nat) ≠ 13 by omega),
      up_ne (show (2:Nat) ≠ 12 by omega), up_ne (show (2:Nat) ≠ 17 by omega),
      up_ne (show (2:Nat) ≠ 20 by omega), hf2]
  have g7 : (up (up (up (up (up f 20 (2 * n + 23 + n / 2 + k)) 17 (instA x (n / 2 + (k - 1)))) 12 0) 13 0) 14 0) 7 = n := by
    rw [up_ne (show (7:Nat) ≠ 14 by omega), up_ne (show (7:Nat) ≠ 13 by omega),
      up_ne (show (7:Nat) ≠ 12 by omega), up_ne (show (7:Nat) ≠ 17 by omega),
      up_ne (show (7:Nat) ≠ 20 by omega), hf7]
  have g8 : (up (up (up (up (up f 20 (2 * n + 23 + n / 2 + k)) 17 (instA x (n / 2 + (k - 1)))) 12 0) 13 0) 14 0) 8 = 2 * n + 23 := by
    rw [up_ne (show (8:Nat) ≠ 14 by omega), up_ne (show (8:Nat) ≠ 13 by omega),
      up_ne (show (8:Nat) ≠ 12 by omega), up_ne (show (8:Nat) ≠ 17 by omega),
      up_ne (show (8:Nat) ≠ 20 by omega), hf8]
  have g10 : (up (up (up (up (up f 20 (2 * n + 23 + n / 2 + k)) 17 (instA x (n / 2 + (k - 1)))) 12 0) 13 0) 14 0) 10 = n / 2 + k := by
    rw [up_ne (show (10:Nat) ≠ 14 by omega), up_ne (show (10:Nat) ≠ 13 by omega),
      up_ne (show (10:Nat) ≠ 12 by omega), up_ne (show (10:Nat) ≠ 17 by omega),
      up_ne (show (10:Nat) ≠ 20 by omega), hf10]
  have h0lt : (0:Nat) < 2 ^ w := Nat.one_le_two_pow (n := w)
  have gfit : ∀ q, (up (up (up (up (up f 20 (2 * n + 23 + n / 2 + k)) 17 (instA x (n / 2 + (k - 1)))) 12 0) 13 0) 14 0) q < 2 ^ w :=
    up_fit (up_fit (up_fit hfit2 h0lt) h0lt) h0lt
  have hgsrc : ∀ q, q < L → (up (up (up (up (up f 20 (2 * n + 23 + n / 2 + k)) 17 (instA x (n / 2 + (k - 1)))) 12 0) 13 0) 14 0) (b + q) = (halfSums (fun i => instA x (n / 2 + i)) (k - 1)).getD q 0 := by
    intro q hq
    rw [up_ne (show b + q ≠ 14 by omega), up_ne (show b + q ≠ 13 by omega),
      up_ne (show b + q ≠ 12 by omega), up_ne (show b + q ≠ 17 by omega),
      up_ne (show b + q ≠ 20 by omega), ← harr, getD_arrL hq]
  have hsL' : (halfSums (fun i => instA x (n / 2 + i)) (k - 1)).length = L := by
    rw [length_halfSums, hL]
  have hbL : b + L < 2 ^ w := haddr _ (by omega)
  have hdL : d + 2 * L < 2 ^ w := haddr _ (by omega)
  have h2L : 2 * L < 2 ^ w := haddr _ (by omega)
  have hdisj : ∀ p q, p < 2 * L → q < L → d + p ≠ b + q := by
    intro p q hp hq
    rcases hbases with ⟨hb, hd⟩|⟨hd, hb⟩ <;> omega
  have hout : halfSums (fun i => instA x (n / 2 + i)) k
      = mmerge (halfSums (fun i => instA x (n / 2 + i)) (k - 1))
          ((halfSums (fun i => instA x (n / 2 + i)) (k - 1)).map (fun z => z + instA x (n / 2 + (k - 1)))) := by
    rw [show k = (k - 1) + 1 from by omega, halfSums,
        show k - 1 + 1 - 1 = k - 1 from by omega]
  obtain ⟨c2, fm, hc2, hex2, harrm, h12m, h14m, hfitm, hpm⟩ :=
    merge2_exec ρ (2 * L) L b d (instA x (n / 2 + (k - 1))) (halfSums (fun i => instA x (n / 2 + i)) (k - 1))
      (halfSums (fun i => instA x (n / 2 + i)) k) (up (up (up (up (up f 20 (2 * n + 23 + n / 2 + k)) 17 (instA x (n / 2 + (k - 1)))) 12 0) 13 0) 14 0) 0 0 0 (S - 5) r hsL'
      (by omega) (by omega) (by omega) g12 g13 g14 g11 g17 g18 g19 g1 g2
      hgsrc (fun v hv => halfSumAddFit2 (by omega) hw (k - 1) (by omega) v hv)
      (by exact rfl) (by exact hout) hout gfit hbL hdL h2L hb33 hd33 hdisj
      (by omega) (by omega)
  have fm11 : fm 11 = L := by
    rw [hpm 11 (mreg_ne_small hd33 (Or.inl (by omega))), g11]
  have fm18 : fm 18 = b := by
    rw [hpm 18 (mreg_ne_small hd33 (Or.inr (Or.inl ⟨by omega, by omega⟩))), g18]
  have fm19 : fm 19 = d := by
    rw [hpm 19 (mreg_ne_small hd33 (Or.inr (Or.inl ⟨by omega, by omega⟩))), g19]
  have fm1 : fm 1 = 1 := by rw [hpm 1 (mreg_ne_small hd33 (Or.inl (by omega))), g1]
  have fm2 : fm 2 = 0 := by rw [hpm 2 (mreg_ne_small hd33 (Or.inl (by omega))), g2]
  have fm7 : fm 7 = n := by rw [hpm 7 (mreg_ne_small hd33 (Or.inl (by omega))), g7]
  have fm8 : fm 8 = 2 * n + 23 := by
    rw [hpm 8 (mreg_ne_small hd33 (Or.inl (by omega))), g8]
  have fm10 : fm 10 = n / 2 + k := by rw [hpm 10 (mreg_ne_small hd33 (Or.inl (by omega))), g10]
  have htail : exec prog2 ρ (S - 5 - c2) 207 r (memOf w fm)
      = exec prog2 ρ (S - 5 - c2 - 6) 213 r (memOf w (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (n / 2 + k + 1)) 21 (n + 1))) :=
    lswap2_exec fm11 fm1 fm2 fm7 fm10 fm18 fm19
      (show prog2.getD 207 Instr.reject = Instr.add 11 11 11 by rfl)
      (show prog2.getD 208 Instr.reject = Instr.add 20 18 2 by rfl)
      (show prog2.getD 209 Instr.reject = Instr.add 18 19 2 by rfl)
      (show prog2.getD 210 Instr.reject = Instr.add 19 20 2 by rfl)
      (show prog2.getD 211 Instr.reject = Instr.add 10 10 1 by rfl)
      (show prog2.getD 212 Instr.reject = Instr.add 21 7 1 by rfl)
      (by omega)
  have f'10 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (n / 2 + k + 1)) 21 (n + 1)) 10 = n / 2 + k + 1 := by
    rw [up_ne (show (10:Nat) ≠ 21 by omega), up_eq]
  have f'11 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (n / 2 + k + 1)) 21 (n + 1)) 11 = 2 * L := by
    rw [up_ne (show (11:Nat) ≠ 21 by omega), up_ne (show (11:Nat) ≠ 10 by omega),
      up_ne (show (11:Nat) ≠ 19 by omega), up_ne (show (11:Nat) ≠ 18 by omega),
      up_ne (show (11:Nat) ≠ 20 by omega), up_eq]
  have f'18 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (n / 2 + k + 1)) 21 (n + 1)) 18 = d := by
    rw [up_ne (show (18:Nat) ≠ 21 by omega), up_ne (show (18:Nat) ≠ 10 by omega),
      up_ne (show (18:Nat) ≠ 19 by omega), up_eq]
  have f'19 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (n / 2 + k + 1)) 21 (n + 1)) 19 = b := by
    rw [up_ne (show (19:Nat) ≠ 21 by omega), up_ne (show (19:Nat) ≠ 10 by omega),
      up_eq]
  have f'21 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (n / 2 + k + 1)) 21 (n + 1)) 21 = n + 1 := by rw [up_eq]
  have f'arr : arrL (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (n / 2 + k + 1)) 21 (n + 1)) d (2 * L) = halfSums (fun i => instA x (n / 2 + i)) k := by
    rw [arrL_up_out (fun q _ => show (21:Nat) ≠ d + q by omega),
        arrL_up_out (fun q _ => show (10:Nat) ≠ d + q by omega),
        arrL_up_out (fun q _ => show (19:Nat) ≠ d + q by omega),
        arrL_up_out (fun q _ => show (18:Nat) ≠ d + q by omega),
        arrL_up_out (fun q _ => show (20:Nat) ≠ d + q by omega),
        arrL_up_out (fun q _ => show (11:Nat) ≠ d + q by omega),
        harrm]
  have f'1 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (n / 2 + k + 1)) 21 (n + 1)) 1 = 1 := by
    rw [up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 10 by omega),
      up_ne (show (1:Nat) ≠ 19 by omega), up_ne (show (1:Nat) ≠ 18 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 11 by omega), fm1]
  have f'2 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (n / 2 + k + 1)) 21 (n + 1)) 2 = 0 := by
    rw [up_ne (show (2:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 10 by omega),
      up_ne (show (2:Nat) ≠ 19 by omega), up_ne (show (2:Nat) ≠ 18 by omega),
      up_ne (show (2:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 11 by omega), fm2]
  have f'7 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (n / 2 + k + 1)) 21 (n + 1)) 7 = n := by
    rw [up_ne (show (7:Nat) ≠ 21 by omega), up_ne (show (7:Nat) ≠ 10 by omega),
      up_ne (show (7:Nat) ≠ 19 by omega), up_ne (show (7:Nat) ≠ 18 by omega),
      up_ne (show (7:Nat) ≠ 20 by omega), up_ne (show (7:Nat) ≠ 11 by omega), fm7]
  have f'8 : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (n / 2 + k + 1)) 21 (n + 1)) 8 = 2 * n + 23 := by
    rw [up_ne (show (8:Nat) ≠ 21 by omega), up_ne (show (8:Nat) ≠ 10 by omega),
      up_ne (show (8:Nat) ≠ 19 by omega), up_ne (show (8:Nat) ≠ 18 by omega),
      up_ne (show (8:Nat) ≠ 20 by omega), up_ne (show (8:Nat) ≠ 11 by omega), fm8]
  have f'fit : ∀ q, (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (n / 2 + k + 1)) 21 (n + 1)) q < 2 ^ w :=
    up_fit (up_fit (up_fit (up_fit (up_fit (up_fit hfitm h2L) (haddr _ (by rw [hBD]; omega)))
      (haddr _ (by rw [hBD]; omega))) (haddr _ (by rw [hBD]; omega))) (haddr _ (by rw [hBD]; omega)))
      (haddr _ (by rw [hBD]; omega))
  have hsub : ∀ c, MReg d L c → AReg2 n c := by
    intro c hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|harr
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · rcases hbases with ⟨hb, hd⟩|⟨hd, hb⟩
      · exact Or.inr ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
  have hpres5 : Pres (AReg2 n) f
      (up (up (up (up (up f 20 (2 * n + 23 + n / 2 + k)) 17 (instA x (n / 2 + (k - 1)))) 12 0) 13 0) 14 0) := by
    refine pres_trans (pres_up (c := 20) (v := 2 * n + 23 + n / 2 + k) (Or.inl (by omega))) ?_
    refine pres_trans (pres_up (c := 17) (v := instA x (n / 2 + (k - 1))) (Or.inl (by omega))) ?_
    refine pres_trans (pres_up (c := 12) (v := 0) (Or.inl (by omega))) ?_
    refine pres_trans (pres_up (c := 13) (v := 0) (Or.inl (by omega))) ?_
    exact pres_up (c := 14) (v := 0) (Or.inl (by omega))
  have hpresf : Pres (AReg2 n) f fm := pres_trans hpres5 (pres_mono hsub hpm)
  have hPA : Pres (AReg2 n) f (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (n / 2 + k + 1)) 21 (n + 1)) := by
    refine pres_trans hpresf ?_
    refine pres_trans (pres_up (c := 11) (v := 2 * L) (Or.inl (by omega))) ?_
    refine pres_trans (pres_up (c := 20) (v := b) (Or.inl (by omega))) ?_
    refine pres_trans (pres_up (c := 18) (v := d) (Or.inl (by omega))) ?_
    refine pres_trans (pres_up (c := 19) (v := b) (Or.inl (by omega))) ?_
    refine pres_trans (pres_up (c := 10) (v := n / 2 + k + 1) (Or.inl (by omega))) ?_
    exact pres_up (c := 21) (v := n + 1) (Or.inl (by omega))
  have f'6f : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (n / 2 + k + 1)) 21 (n + 1)) 6 = f 6 := by
    rw [up_ne (show (6:Nat) ≠ 21 by omega), up_ne (show (6:Nat) ≠ 10 by omega),
      up_ne (show (6:Nat) ≠ 19 by omega), up_ne (show (6:Nat) ≠ 18 by omega),
      up_ne (show (6:Nat) ≠ 20 by omega), up_ne (show (6:Nat) ≠ 11 by omega),
      hpm 6 (mreg_ne_small hd33 (Or.inl (by omega))),
      up_ne (show (6:Nat) ≠ 14 by omega), up_ne (show (6:Nat) ≠ 13 by omega),
      up_ne (show (6:Nat) ≠ 12 by omega), up_ne (show (6:Nat) ≠ 17 by omega),
      up_ne (show (6:Nat) ≠ 20 by omega)]
  have hf9f : (up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (n / 2 + k + 1)) 21 (n + 1)) 9 = f 9 := by
    rw [up_ne (show (9:Nat) ≠ 21 by omega), up_ne (show (9:Nat) ≠ 10 by omega),
      up_ne (show (9:Nat) ≠ 19 by omega), up_ne (show (9:Nat) ≠ 18 by omega),
      up_ne (show (9:Nat) ≠ 20 by omega), up_ne (show (9:Nat) ≠ 11 by omega),
      hpm 9 (mreg_ne_small hd33 (Or.inl (by omega))),
      up_ne (show (9:Nat) ≠ 14 by omega), up_ne (show (9:Nat) ≠ 13 by omega),
      up_ne (show (9:Nat) ≠ 12 by omega), up_ne (show (9:Nat) ≠ 17 by omega),
      up_ne (show (9:Nat) ≠ 20 by omega)]
  refine ⟨5 + c2 + 6, up (up (up (up (up (up fm 11 (2 * L)) 20 b) 18 d) 19 b) 10 (n / 2 + k + 1)) 21 (n + 1), by omega, ?_, f'10, f'11, f'18, f'19, f'21, f'arr,
    f'1, f'2, f'7, f'8, f'6f, hf9f, f'fit, hPA⟩
  rw [hwalk5, hex2, htail]
  simp only [Nat.sub_sub]

/-! ## §6. The round loop (pc 164 → 215) -/

set_option maxHeartbeats 12000000 in
/-- All rounds `k..m2` from pc 164 (`m2 = n - n/2`): each round merges,
doubles `L`, swaps the pointers; after round `m2` the guard at 213 falls
through and the post-loop `add 19 18 2` (pc 214) lands at canon's entry
(pc 215) with `halfSums (fun i => instA x (n/2+i)) m2` at `[rSRC]` and
`[rDST]`.  The `+ 1` in the budget is pc 214's step. -/
theorem lround2_exec {w n : Nat} (ρ : Nat → BitVec w) {x : Instance n}
    (hn : 3 ≤ n) (hw : wordLength n x.bits ≤ w) :
    ∀ F (k L b d : Nat) (f : Nat → Nat) (S r : Nat),
    1 ≤ k → k ≤ n - n / 2 → L = 2 ^ (k - 1) →
    f 1 = 1 → f 2 = 0 → f 7 = n → f 8 = 2 * n + 23 →
    f 10 = n / 2 + k → f 11 = L → f 18 = b → f 19 = d →
    arrL f b L = halfSums (fun i => instA x (n / 2 + i)) (k - 1) →
    (b = BD2 n ∧ d = BD2 n + 2 ^ (n - n / 2) + 1 ∨
      d = BD2 n ∧ b = BD2 n + 2 ^ (n - n / 2) + 1) →
    (∀ i, 1 ≤ i → i ≤ n - n / 2 →
      f (2 * n + 23 + n / 2 + i) = instA x (n / 2 + (i - 1))) →
    (∀ i, i < n → instA x i < 2 ^ w) →
    (∀ q, f q < 2 ^ w) →
    (∀ c, c ≤ BD2 n + 2 * 2 ^ (n - n / 2) + 1 → c < 2 ^ w) →
    n - n / 2 + 1 - k ≤ F →
    44 * (2 ^ (n - n / 2) - 2 ^ (k - 1)) + 24 * (n - n / 2 - k + 1) + 1 ≤ S →
    ∃ c f' bd, c ≤ 44 * (2 ^ (n - n / 2) - 2 ^ (k - 1)) + 24 * (n - n / 2 - k + 1) + 1 ∧
      exec prog2 ρ S 164 r (memOf w f) = exec prog2 ρ (S - c) 215 r (memOf w f') ∧
      f' 10 = n + 1 ∧ f' 11 = 2 ^ (n - n / 2) ∧ f' 18 = bd ∧ f' 19 = bd ∧
      (bd = BD2 n ∨ bd = BD2 n + 2 ^ (n - n / 2) + 1) ∧
      arrL f' bd (2 ^ (n - n / 2))
        = halfSums (fun i => instA x (n / 2 + i)) (n - n / 2) ∧
      f' 1 = 1 ∧ f' 2 = 0 ∧ f' 7 = n ∧ f' 8 = 2 * n + 23 ∧
      f' 6 = f 6 ∧ f' 9 = f 9 ∧
      (∀ q, f' q < 2 ^ w) ∧ Pres (AReg2 n) f f' := by
  intro F
  induction F with
  | zero =>
    intro k L b d f S r hk1 hkh hL hf1 hf2 hf7 hf8 hf10 hf11 hf18 hf19
      harr hbases hrel hin hfit haddr hfuel hS
    omega
  | succ F ih =>
    intro k L b d f S r hk1 hkh hL hf1 hf2 hf7 hf8 hf10 hf11 hf18 hf19
      harr hbases hrel hin hfit haddr hfuel hS
    have hLm : L ≤ 2 ^ (n - n / 2) := by
      rw [hL]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have h2k : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [← Nat.pow_succ', show (k - 1).succ = k from by omega]
    have hk2m : 2 ^ k ≤ 2 ^ (n - n / 2) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h2p1 : 2 ^ (n - n / 2 + 1) = 2 * 2 ^ (n - n / 2) := by
      rw [Nat.pow_succ, Nat.mul_comm]
    obtain ⟨c1, fr, hc1, hex1, hfr10, hfr11, hfr18, hfr19, hfr21, hfrarr,
      hfr1, hfr2, hfr7, hfr8, hfr6, hfr9, hfrfit, hfrpres⟩ :=
      round2_exec ρ hn hw k L b d f S r hk1 hkh hL hf1 hf2 hf7 hf8 hf10 hf11
        hf18 hf19 harr hbases hrel hin hfit haddr (by omega)
    have hdle : d ≤ BD2 n + 2 * 2 ^ (n - n / 2) + 1 := by
      rcases hbases with ⟨_, hd⟩ | ⟨hd, _⟩ <;> omega
    have h44 : ∀ (A B : Nat), B ≤ A → 44 * (A - B) = 44 * A - 44 * B := by
      intro A B hAB; omega
    have hsplit_g : 44 * (2 ^ (n - n / 2) - 2 ^ k)
        = 44 * 2 ^ (n - n / 2) - 44 * 2 ^ k := h44 _ _ (by omega)
    have hsplit_j : 44 * (2 ^ (n - n / 2) - 2 ^ (k - 1))
        = 44 * 2 ^ (n - n / 2) - 44 * 2 ^ (k - 1) := h44 _ _ (by omega)
    by_cases hkl : k < n - n / 2
    · -- guard taken: round k+1 from pc 164
      have hwalk : exec prog2 ρ S 164 r (memOf w f)
          = exec prog2 ρ (S - (c1 + 1)) 164 r (memOf w fr) := by
        rw [hex1,
          exec_blt_lt_step (by omega)
            (show prog2.getD 213 Instr.reject = Instr.blt 10 21 164 by rfl) hfrfit
            (by rw [hfr10, hfr21]; omega)]
        simp only [Nat.sub_sub]
      have hL' : 2 * L = 2 ^ (k + 1 - 1) := by
        rw [show k + 1 - 1 = k from by omega, h2k, ← hL]
      have hbases' : (d = BD2 n ∧ b = BD2 n + 2 ^ (n - n / 2) + 1 ∨
          b = BD2 n ∧ d = BD2 n + 2 ^ (n - n / 2) + 1) := by
        rcases hbases with ⟨hb, hd⟩|⟨hd, hb⟩
        · exact Or.inr ⟨hb, hd⟩
        · exact Or.inl ⟨hd, hb⟩
      have hrel' : ∀ i, 1 ≤ i → i ≤ n - n / 2 →
          fr (2 * n + 23 + n / 2 + i) = instA x (n / 2 + (i - 1)) := by
        intro i hi1 hin'
        have hnA : ¬ AReg2 n (2 * n + 23 + n / 2 + i) :=
          block_not_AReg2 (n := n) (by omega) (by omega) (by omega)
        rw [hfrpres _ hnA]
        exact hrel i hi1 hin'
      obtain ⟨c2, f2', bd, hc2, hex2, hf210, hf211, hf218, hf2bd, hf2disj,
        hf2arr, hf21, hf22, hf27, hf28, hf26, hf29, hf2fit, hf2pres⟩ :=
        ih (k + 1) (2 * L) d b fr (S - (c1 + 1)) r (by omega) (by omega)
          hL' hfr1 hfr2 hfr7 hfr8 hfr10 hfr11 hfr18 hfr19
          (by rw [show k + 1 - 1 = k from by omega]; exact hfrarr)
          hbases' hrel' hin hfrfit haddr (by omega)
          (by
            have hc1' : c1 ≤ 44 * 2 ^ (k - 1) + 23 := by rw [hL] at hc1; exact hc1
            exact ih_budget_step (n - n / 2) k (n - n / 2) S c1 h2k hk2m
              (lt_succ_le k (n - n / 2) hkl) hc1' hS)
      refine ⟨c1 + 1 + c2, f2', bd, by omega, ?_, hf210, hf211, hf218, hf2bd,
        hf2disj, hf2arr, hf21, hf22, hf27, hf28, (by rw [hf26]; exact hfr6),
        (by rw [hf29]; exact hfr9), hf2fit, pres_trans hfrpres hf2pres⟩
      rw [hwalk, hex2]
      rw [show S - (c1 + 1) - c2 = S - (c1 + 1 + c2) from by omega]
    · -- k = n - n/2: guard falls through, pc 214's add lands at 215
      have hkm : k = n - n / 2 := by omega
      have h2m2 : 2 * L = 2 ^ (n - n / 2) := by
        rw [hL, ← h2k, hkm]
      have hsplit_k : 44 * (2 ^ k - 2 ^ (k - 1))
        = 44 * 2 ^ k - 44 * 2 ^ (k - 1) := h44 _ _ (by omega)
      have hd33 : 33 ≤ d := by
        rcases hbases with ⟨_, hd⟩ | ⟨hd, _⟩
        · rw [show BD2 n = 3 * n + 25 + 2 * 2 ^ (n / 2) + 2 from rfl] at hd; omega
        · rw [show BD2 n = 3 * n + 25 + 2 * 2 ^ (n / 2) + 2 from rfl] at hd; omega
      have hfr10' : fr 10 = n + 1 := by rw [hfr10, hkm]; omega
      have hwalkE : exec prog2 ρ S 164 r (memOf w f)
          = exec prog2 ρ (S - (c1 + 2)) 215 r (memOf w (up fr 19 d)) := by
        rw [hex1,
          exec_blt_ge_step (by omega)
            (show prog2.getD 213 Instr.reject = Instr.blt 10 21 164 by rfl) hfrfit
            (by rw [hfr10, hfr21, hkm]; omega),
          exec_add_step (by omega)
            (show prog2.getD 214 Instr.reject = Instr.add 19 18 2 by rfl),
          show fr 18 + fr 2 = d from by rw [hfr18, hfr2, Nat.add_zero]]
        simp only [Nat.sub_sub]
      refine ⟨c1 + 2, up fr 19 d, d, (by rw [← hkm]; rw [hsplit_k]; omega), hwalkE,
        by rw [up_ne (show (10:Nat) ≠ 19 by omega)]; exact hfr10',
        by rw [up_ne (show (11:Nat) ≠ 19 by omega), hfr11]; exact h2m2,
        by rw [up_ne (show (18:Nat) ≠ 19 by omega)]; exact hfr18,
        (up_eq fr 19 d), ?_, ?_, hfr1, hfr2, hfr7, hfr8,
        by rw [up_ne (show (6:Nat) ≠ 19 by omega)]; exact hfr6,
        by rw [up_ne (show (9:Nat) ≠ 19 by omega)]; exact hfr9,
        up_fit hfrfit (haddr _ hdle),
        pres_trans hfrpres (pres_up (c := 19) (v := d) (Or.inl (by omega)))⟩
      · rcases hbases with ⟨hb, hd⟩|⟨hd, hb⟩
        · exact Or.inr hd
        · exact Or.inl hd
      · rw [hkm] at hfrarr
        rw [arrL_up_out (fun q (_ : q < 2 ^ (n - n / 2)) => Nat.ne_of_lt (d33_lt d q hd33)), ← h2m2]
        exact hfrarr


set_option maxHeartbeats 12000000 in
/-! ## §7. The phase driver (pc 148 → 215). -/

/-- PH2: running `prog2` from pc 148 with the post-phaseA state builds
the sorted subset sums of the second half (the family
`fun i => instA x (n/2+i)`, `2^(n−n/2)` entries) at a fresh base `bd2`
inside `AReg2 n`'s window, and lands at canon's entry (pc 215) with
`[19] = [18] = bd2`, `[11] = 2^(n−n/2)`, `[10] = n+1`, `[9] = n/2`, and
`[6] = bd1` (the first-half base, handed to canon/scanB).  Budget:
`16` (setup) `+ 44·(2^(n−n/2)−1) + 24·(n−n/2) + 1` (rounds + guard + 214). -/
theorem phaseA2_exec {w n : Nat} (ρ : Nat → BitVec w) {x : Instance n}
    (hn : 4 ≤ n) (hw : wordLength n x.bits ≤ w)
    (f0 : Nat → Nat) (r S : Nat)
    (hfit : ∀ q, f0 q < 2 ^ w)
    (h1 : f0 1 = 1) (h2 : f0 2 = 0) (h7 : f0 7 = n) (h8 : f0 8 = 2 * n + 23)
    (h9 : f0 9 = n / 2) (h10 : f0 10 = n / 2 + 1)
    (hbd1 : f0 18 = bd1) (hb1 : bd1 = 3 * n + 25 ∨ bd1 = 3 * n + 25 + 2 ^ (n / 2) + 1)
    (harr : arrL f0 bd1 (2 ^ (n / 2)) = halfSums (instA x) (n / 2))
    (haddr : ∀ c, c ≤ BD2 n + 2 * 2 ^ (n - n / 2) + 1 → c < 2 ^ w)
    (hrel : ∀ i, 1 ≤ i → i ≤ n → f0 (2 * n + 23 + i) = instA x (i - 1))
    (hin : ∀ i, i < n → instA x i < 2 ^ w)
    (hS : 17 + 44 * (2 ^ (n - n / 2) - 1) + 24 * (n - n / 2) ≤ S) :
    ∃ c f' bd2, c ≤ 17 + 44 * (2 ^ (n - n / 2) - 1) + 24 * (n - n / 2) ∧
      exec prog2 ρ S 148 r (memOf w f0) = exec prog2 ρ (S - c) pcCanon r (memOf w f') ∧
      f' 10 = n + 1 ∧ f' 11 = 2 ^ (n - n / 2) ∧ f' 19 = bd2 ∧ f' 18 = bd2 ∧
      (bd2 = BD2 n ∨ bd2 = BD2 n + 2 ^ (n - n / 2) + 1) ∧
      arrL f' bd2 (2 ^ (n - n / 2))
        = halfSums (fun i => instA x (n / 2 + i)) (n - n / 2) ∧
      f' 6 = bd1 ∧ f' 1 = 1 ∧ f' 2 = 0 ∧ f' 7 = n ∧ f' 8 = 2 * n + 23 ∧
      f' 9 = n / 2 ∧
      (∀ q, f' q < 2 ^ w) ∧ Pres (AReg2 n) f0 f' := by
  have h0lt : (0:Nat) < 2 ^ w := Nat.one_le_two_pow (n := w)
  have hBD : BD2 n = 3 * n + 25 + 2 * 2 ^ (n / 2) + 2 := rfl
  have hBDle : BD2 n ≤ 3 * n + 25 + 2 * 2 ^ (n / 2) + 2 + 2 * 2 ^ (n - n / 2) + 1 := by
    rw [hBD]; omega
  have hBDbig : 22 < BD2 n := by
    rw [hBD]
    have h4 : (2:Nat) ^ 2 ≤ 2 ^ (n / 2) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hbd1le : bd1 ≤ 3 * n + 25 + 2 * 2 ^ (n / 2) + 2 + 2 * 2 ^ (n - n / 2) + 1 := by
    rcases hb1 with rfl | rfl
    · omega
    · have hA1 : (1:Nat) ≤ 2 ^ (n / 2) := Nat.one_le_two_pow
      have hD : (0:Nat) ≤ 2 * 2 ^ (n - n / 2) := Nat.zero_le _
      omega
  have haddr' : ∀ c, c ≤ 3 * n + 25 + 2 * 2 ^ (n / 2) + 2 + 2 * 2 ^ (n - n / 2) + 1 →
      c < 2 ^ w := fun c hc => haddr c (by rw [hBD]; omega)
  have f1fit : ∀ q, (up (f0) (6) (bd1)) q < 2 ^ w := up_fit hfit (haddr' _ hbd1le)
  have f2fit : ∀ q, (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) q < 2 ^ w := up_fit f1fit ((haddr' _ (by omega)))
  have f3fit : ∀ q, (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) q < 2 ^ w := up_fit f2fit ((haddr' _ (by omega)))
  have f4fit : ∀ q, (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) q < 2 ^ w := up_fit f3fit ((haddr' _ (by omega)))
  have f5fit : ∀ q, (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) q < 2 ^ w := up_fit f4fit ((haddr' _ (by omega)))
  have f6fit : ∀ q, (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) q < 2 ^ w := up_fit f5fit ((haddr' _ (by omega)))
  have f7fit : ∀ q, (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) q < 2 ^ w := up_fit f6fit ((haddr' _ (by omega)))
  have f8fit : ∀ q, (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) q < 2 ^ w := up_fit f7fit ((haddr' _ (by omega)))
  have f9fit : ∀ q, (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) q < 2 ^ w := up_fit f8fit ((haddr' _ (by omega)))
  have f10fit : ∀ q, (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) q < 2 ^ w := up_fit f9fit ((haddr' _ (by omega)))
  have f11fit : ∀ q, (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) q < 2 ^ w := up_fit f10fit ((haddr' _ (by omega)))
  have f12fit : ∀ q, (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) q < 2 ^ w := up_fit f11fit ((haddr' _ (by omega)))
  have f13fit : ∀ q, (up (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2) + 1)) q < 2 ^ w := up_fit f12fit ((haddr' _ (by omega)))
  have f14fit : ∀ q, (up (up (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2) + 1)) (11) (1)) q < 2 ^ w := up_fit f13fit ((haddr' _ (by omega)))
  have f15fit : ∀ q, (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2) + 1)) (11) (1)) (20) (BD2 n)) q < 2 ^ w := up_fit f14fit ((haddr' _ (by omega)))
  have f16fit : ∀ q, (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2) + 1)) (11) (1)) (20) (BD2 n)) (BD2 n) (0)) q < 2 ^ w := up_fit f15fit h0lt
  have hbd0 : f0 18 + f0 2 = bd1 := by rw [hbd1, h2, Nat.add_zero]
  have e149 : (up (f0) (6) (bd1)) 1 * 2 ^ (up (f0) (6) (bd1)) 10 = 2 ^ (n / 2 + 1) := by
    rw [up_ne (show (1:Nat) ≠ 6 by omega), up_ne (show (10:Nat) ≠ 6 by omega),
      h1, h10, Nat.one_mul]
  have e149lt : (up (f0) (6) (bd1)) 1 * 2 ^ (up (f0) (6) (bd1)) 10 < 2 ^ w := by
    rw [e149]
    exact haddr' _ (by omega)
  have e150 : (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) 8 + (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) 7 = 3 * n + 23 := by
    rw [up_ne (show (8:Nat) ≠ 21 by omega), up_ne (show (7:Nat) ≠ 21 by omega),
      up_ne (show (8:Nat) ≠ 6 by omega), up_ne (show (7:Nat) ≠ 6 by omega), h8, h7]
    omega
  have e151 : (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) 18 + (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) 21 = 3 * n + 23 + 2 ^ (n / 2 + 1) := by
    rw [up_eq, up_ne (show (21:Nat) ≠ 18 by omega), up_eq]
  have e152 : (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) 18 + (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) 1 = 3 * n + 23 + 2 ^ (n / 2 + 1) + 1 := by
    rw [up_eq, up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 6 by omega), h1]
  have e153 : (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) 18 + (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) 1 = 3 * n + 23 + 2 ^ (n / 2 + 1) + 2 := by
    rw [up_eq, up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 6 by omega), h1]
  have e154 : (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) 18 + (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) 1 = 3 * n + 23 + 2 ^ (n / 2 + 1) + 3 := by
    rw [up_eq, up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 6 by omega), h1]
  have e155 : (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) 18 + (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) 1 = BD2 n := by
    rw [up_eq, hBD, Nat.pow_succ, up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 6 by omega), h1]
    omega
  have e156 : (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) 7 - (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) 9 = n - n / 2 := by
    rw [up_ne (show (7:Nat) ≠ 18 by omega), up_ne (show (7:Nat) ≠ 18 by omega), up_ne (show (7:Nat) ≠ 18 by omega), up_ne (show (7:Nat) ≠ 18 by omega), up_ne (show (7:Nat) ≠ 18 by omega), up_ne (show (7:Nat) ≠ 18 by omega), up_ne (show (7:Nat) ≠ 21 by omega), up_ne (show (7:Nat) ≠ 6 by omega), h7, up_ne (show (9:Nat) ≠ 18 by omega), up_ne (show (9:Nat) ≠ 18 by omega), up_ne (show (9:Nat) ≠ 18 by omega), up_ne (show (9:Nat) ≠ 18 by omega), up_ne (show (9:Nat) ≠ 18 by omega), up_ne (show (9:Nat) ≠ 18 by omega), up_ne (show (9:Nat) ≠ 21 by omega), up_ne (show (9:Nat) ≠ 6 by omega), h9]
  have e156le : (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) 9 ≤ (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) 7 := by
    rw [up_ne (show (7:Nat) ≠ 18 by omega), up_ne (show (7:Nat) ≠ 18 by omega), up_ne (show (7:Nat) ≠ 18 by omega), up_ne (show (7:Nat) ≠ 18 by omega), up_ne (show (7:Nat) ≠ 18 by omega), up_ne (show (7:Nat) ≠ 18 by omega), up_ne (show (7:Nat) ≠ 21 by omega), up_ne (show (7:Nat) ≠ 6 by omega), h7, up_ne (show (9:Nat) ≠ 18 by omega), up_ne (show (9:Nat) ≠ 18 by omega), up_ne (show (9:Nat) ≠ 18 by omega), up_ne (show (9:Nat) ≠ 18 by omega), up_ne (show (9:Nat) ≠ 18 by omega), up_ne (show (9:Nat) ≠ 18 by omega), up_ne (show (9:Nat) ≠ 21 by omega), up_ne (show (9:Nat) ≠ 6 by omega), h9]
    omega
  have e157 : (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) 1 + (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) 2 = 1 := by
    rw [up_ne (show (1:Nat) ≠ 22 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 6 by omega), h1, up_ne (show (2:Nat) ≠ 22 by omega), up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 6 by omega), h2, Nat.add_zero]
  have e158 : (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) 21 * 2 ^ (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) 22 = 2 ^ (n - n / 2) := by
    rw [up_eq, up_ne (show (22:Nat) ≠ 21 by omega), up_eq, Nat.one_mul]
  have e158lt : (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) 21 * 2 ^ (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) 22 < 2 ^ w := by
    rw [e158]
    exact haddr' _ (by omega)
  have e159 : (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) 18 + (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) 21 = BD2 n + 2 ^ (n - n / 2) := by
    rw [up_ne (show (18:Nat) ≠ 21 by omega), up_ne (show (18:Nat) ≠ 21 by omega), up_ne (show (18:Nat) ≠ 22 by omega), up_eq, up_eq]
  have e160 : (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) 19 + (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) 1 = BD2 n + 2 ^ (n - n / 2) + 1 := by
    rw [up_eq, up_ne (show (1:Nat) ≠ 19 by omega), up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 22 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 6 by omega), h1]
  have e161 : (up (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2) + 1)) 1 + (up (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2) + 1)) 2 = 1 := by
    rw [up_ne (show (1:Nat) ≠ 19 by omega), up_ne (show (1:Nat) ≠ 19 by omega), up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 22 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 6 by omega), h1, up_ne (show (2:Nat) ≠ 19 by omega), up_ne (show (2:Nat) ≠ 19 by omega), up_ne (show (2:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 22 by omega), up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 6 by omega), h2, Nat.add_zero]
  have e162 : (up (up (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2) + 1)) (11) (1)) 18 + (up (up (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2) + 1)) (11) (1)) 2 = BD2 n := by
    rw [up_ne (show (18:Nat) ≠ 11 by omega), up_ne (show (18:Nat) ≠ 19 by omega), up_ne (show (18:Nat) ≠ 19 by omega), up_ne (show (18:Nat) ≠ 21 by omega), up_ne (show (18:Nat) ≠ 21 by omega), up_ne (show (18:Nat) ≠ 22 by omega), up_eq, up_ne (show (2:Nat) ≠ 11 by omega), up_ne (show (2:Nat) ≠ 19 by omega), up_ne (show (2:Nat) ≠ 19 by omega), up_ne (show (2:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 22 by omega), up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 6 by omega), h2, Nat.add_zero]
  have e163 : (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2) + 1)) (11) (1)) (20) (BD2 n)) 20 = BD2 n := up_eq _ _ _
  have e163b : (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2) + 1)) (11) (1)) (20) (BD2 n)) 2 = 0 := by
    rw [up_ne (show (2:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 11 by omega), up_ne (show (2:Nat) ≠ 19 by omega), up_ne (show (2:Nat) ≠ 19 by omega), up_ne (show (2:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 22 by omega), up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 6 by omega), h2]
  have hsetup : exec prog2 ρ S 148 r (memOf w f0)
      = exec prog2 ρ (S - 16) 164 r (memOf w (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2) + 1)) (11) (1)) (20) (BD2 n)) (BD2 n) (0))) := by
    rw [exec_add_step (by omega)
        (show prog2.getD 148 Instr.reject = Instr.add 6 18 2 by rfl), hbd0,
      exec_shl_step (by omega)
        (show prog2.getD 149 Instr.reject = Instr.shl 21 1 10 by rfl) f1fit e149lt,
      e149,
      exec_add_step (by omega)
        (show prog2.getD 150 Instr.reject = Instr.add 18 8 7 by rfl), e150,
      exec_add_step (by omega)
        (show prog2.getD 151 Instr.reject = Instr.add 18 18 21 by rfl), e151,
      exec_add_step (by omega)
        (show prog2.getD 152 Instr.reject = Instr.add 18 18 1 by rfl), e152,
      exec_add_step (by omega)
        (show prog2.getD 153 Instr.reject = Instr.add 18 18 1 by rfl), e153,
      exec_add_step (by omega)
        (show prog2.getD 154 Instr.reject = Instr.add 18 18 1 by rfl), e154,
      exec_add_step (by omega)
        (show prog2.getD 155 Instr.reject = Instr.add 18 18 1 by rfl), e155,
      exec_sub_step (by omega)
        (show prog2.getD 156 Instr.reject = Instr.sub 22 7 9 by rfl) f8fit e156le,
      e156,
      exec_add_step (by omega)
        (show prog2.getD 157 Instr.reject = Instr.add 21 1 2 by rfl), e157,
      exec_shl_step (by omega)
        (show prog2.getD 158 Instr.reject = Instr.shl 21 21 22 by rfl) f10fit e158lt,
      e158,
      exec_add_step (by omega)
        (show prog2.getD 159 Instr.reject = Instr.add 19 18 21 by rfl), e159,
      exec_add_step (by omega)
        (show prog2.getD 160 Instr.reject = Instr.add 19 19 1 by rfl), e160,
      exec_add_step (by omega)
        (show prog2.getD 161 Instr.reject = Instr.add 11 1 2 by rfl), e161,
      exec_add_step (by omega)
        (show prog2.getD 162 Instr.reject = Instr.add 20 18 2 by rfl), e162,
      exec_store_step (by omega)
        (show prog2.getD 163 Instr.reject = Instr.store 20 2 by rfl) f15fit,
      e163, e163b]
    simp only [Nat.sub_sub, Nat.reduceAdd]
  have hf16_BD2_n : (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2) + 1)) (11) (1)) (20) (BD2 n)) (BD2 n) (0)) (BD2 n) = 0 := by
    rw [up_eq]
  have hf16_6 : (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2) + 1)) (11) (1)) (20) (BD2 n)) (BD2 n) (0)) (6) = bd1 := by
    rw [up_ne (show (6:Nat) ≠ BD2 n by omega), up_ne (show (6:Nat) ≠ 20 by omega), up_ne (show (6:Nat) ≠ 11 by omega), up_ne (show (6:Nat) ≠ 19 by omega), up_ne (show (6:Nat) ≠ 19 by omega), up_ne (show (6:Nat) ≠ 21 by omega), up_ne (show (6:Nat) ≠ 21 by omega), up_ne (show (6:Nat) ≠ 22 by omega), up_ne (show (6:Nat) ≠ 18 by omega), up_ne (show (6:Nat) ≠ 18 by omega), up_ne (show (6:Nat) ≠ 18 by omega), up_ne (show (6:Nat) ≠ 18 by omega), up_ne (show (6:Nat) ≠ 18 by omega), up_ne (show (6:Nat) ≠ 18 by omega), up_ne (show (6:Nat) ≠ 21 by omega), up_eq]
  have hf16_20 : (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2) + 1)) (11) (1)) (20) (BD2 n)) (BD2 n) (0)) (20) = BD2 n := by
    rw [up_ne (show (20:Nat) ≠ BD2 n by omega), up_eq]
  have hf16_11 : (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2) + 1)) (11) (1)) (20) (BD2 n)) (BD2 n) (0)) (11) = 1 := by
    rw [up_ne (show (11:Nat) ≠ BD2 n by omega), up_ne (show (11:Nat) ≠ 20 by omega), up_eq]
  have hf16_19 : (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2) + 1)) (11) (1)) (20) (BD2 n)) (BD2 n) (0)) (19) = BD2 n + 2 ^ (n - n / 2) + 1 := by
    rw [up_ne (show (19:Nat) ≠ BD2 n by omega), up_ne (show (19:Nat) ≠ 20 by omega), up_ne (show (19:Nat) ≠ 11 by omega), up_eq]
  have hf16_21 : (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2) + 1)) (11) (1)) (20) (BD2 n)) (BD2 n) (0)) (21) = 2 ^ (n - n / 2) := by
    rw [up_ne (show (21:Nat) ≠ BD2 n by omega), up_ne (show (21:Nat) ≠ 20 by omega), up_ne (show (21:Nat) ≠ 11 by omega), up_ne (show (21:Nat) ≠ 19 by omega), up_ne (show (21:Nat) ≠ 19 by omega), up_eq]
  have hf16_18 : (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2) + 1)) (11) (1)) (20) (BD2 n)) (BD2 n) (0)) (18) = BD2 n := by
    rw [up_ne (show (18:Nat) ≠ BD2 n by omega), up_ne (show (18:Nat) ≠ 20 by omega), up_ne (show (18:Nat) ≠ 11 by omega), up_ne (show (18:Nat) ≠ 19 by omega), up_ne (show (18:Nat) ≠ 19 by omega), up_ne (show (18:Nat) ≠ 21 by omega), up_ne (show (18:Nat) ≠ 21 by omega), up_ne (show (18:Nat) ≠ 22 by omega), up_eq]
  have hf16_9 : (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2) + 1)) (11) (1)) (20) (BD2 n)) (BD2 n) (0)) (9) = n / 2 := by
    rw [up_ne (show (9:Nat) ≠ BD2 n by omega), up_ne (show (9:Nat) ≠ 20 by omega), up_ne (show (9:Nat) ≠ 11 by omega), up_ne (show (9:Nat) ≠ 19 by omega), up_ne (show (9:Nat) ≠ 19 by omega), up_ne (show (9:Nat) ≠ 21 by omega), up_ne (show (9:Nat) ≠ 21 by omega), up_ne (show (9:Nat) ≠ 22 by omega), up_ne (show (9:Nat) ≠ 18 by omega), up_ne (show (9:Nat) ≠ 18 by omega), up_ne (show (9:Nat) ≠ 18 by omega), up_ne (show (9:Nat) ≠ 18 by omega), up_ne (show (9:Nat) ≠ 18 by omega), up_ne (show (9:Nat) ≠ 18 by omega), up_ne (show (9:Nat) ≠ 21 by omega), up_ne (show (9:Nat) ≠ 6 by omega), h9]
  have hf16_10 : (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2) + 1)) (11) (1)) (20) (BD2 n)) (BD2 n) (0)) (10) = n / 2 + 1 := by
    rw [up_ne (show (10:Nat) ≠ BD2 n by omega), up_ne (show (10:Nat) ≠ 20 by omega), up_ne (show (10:Nat) ≠ 11 by omega), up_ne (show (10:Nat) ≠ 19 by omega), up_ne (show (10:Nat) ≠ 19 by omega), up_ne (show (10:Nat) ≠ 21 by omega), up_ne (show (10:Nat) ≠ 21 by omega), up_ne (show (10:Nat) ≠ 22 by omega), up_ne (show (10:Nat) ≠ 18 by omega), up_ne (show (10:Nat) ≠ 18 by omega), up_ne (show (10:Nat) ≠ 18 by omega), up_ne (show (10:Nat) ≠ 18 by omega), up_ne (show (10:Nat) ≠ 18 by omega), up_ne (show (10:Nat) ≠ 18 by omega), up_ne (show (10:Nat) ≠ 21 by omega), up_ne (show (10:Nat) ≠ 6 by omega), h10]
  have hf16_7 : (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2) + 1)) (11) (1)) (20) (BD2 n)) (BD2 n) (0)) (7) = n := by
    rw [up_ne (show (7:Nat) ≠ BD2 n by omega), up_ne (show (7:Nat) ≠ 20 by omega), up_ne (show (7:Nat) ≠ 11 by omega), up_ne (show (7:Nat) ≠ 19 by omega), up_ne (show (7:Nat) ≠ 19 by omega), up_ne (show (7:Nat) ≠ 21 by omega), up_ne (show (7:Nat) ≠ 21 by omega), up_ne (show (7:Nat) ≠ 22 by omega), up_ne (show (7:Nat) ≠ 18 by omega), up_ne (show (7:Nat) ≠ 18 by omega), up_ne (show (7:Nat) ≠ 18 by omega), up_ne (show (7:Nat) ≠ 18 by omega), up_ne (show (7:Nat) ≠ 18 by omega), up_ne (show (7:Nat) ≠ 18 by omega), up_ne (show (7:Nat) ≠ 21 by omega), up_ne (show (7:Nat) ≠ 6 by omega), h7]
  have hf16_8 : (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2) + 1)) (11) (1)) (20) (BD2 n)) (BD2 n) (0)) (8) = 2 * n + 23 := by
    rw [up_ne (show (8:Nat) ≠ BD2 n by omega), up_ne (show (8:Nat) ≠ 20 by omega), up_ne (show (8:Nat) ≠ 11 by omega), up_ne (show (8:Nat) ≠ 19 by omega), up_ne (show (8:Nat) ≠ 19 by omega), up_ne (show (8:Nat) ≠ 21 by omega), up_ne (show (8:Nat) ≠ 21 by omega), up_ne (show (8:Nat) ≠ 22 by omega), up_ne (show (8:Nat) ≠ 18 by omega), up_ne (show (8:Nat) ≠ 18 by omega), up_ne (show (8:Nat) ≠ 18 by omega), up_ne (show (8:Nat) ≠ 18 by omega), up_ne (show (8:Nat) ≠ 18 by omega), up_ne (show (8:Nat) ≠ 18 by omega), up_ne (show (8:Nat) ≠ 21 by omega), up_ne (show (8:Nat) ≠ 6 by omega), h8]
  have hf16_1 : (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2) + 1)) (11) (1)) (20) (BD2 n)) (BD2 n) (0)) (1) = 1 := by
    rw [up_ne (show (1:Nat) ≠ BD2 n by omega), up_ne (show (1:Nat) ≠ 20 by omega), up_ne (show (1:Nat) ≠ 11 by omega), up_ne (show (1:Nat) ≠ 19 by omega), up_ne (show (1:Nat) ≠ 19 by omega), up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 22 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 18 by omega), up_ne (show (1:Nat) ≠ 21 by omega), up_ne (show (1:Nat) ≠ 6 by omega), h1]
  have hf16_2 : (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2) + 1)) (11) (1)) (20) (BD2 n)) (BD2 n) (0)) (2) = 0 := by
    rw [up_ne (show (2:Nat) ≠ BD2 n by omega), up_ne (show (2:Nat) ≠ 20 by omega), up_ne (show (2:Nat) ≠ 11 by omega), up_ne (show (2:Nat) ≠ 19 by omega), up_ne (show (2:Nat) ≠ 19 by omega), up_ne (show (2:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 22 by omega), up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 18 by omega), up_ne (show (2:Nat) ≠ 21 by omega), up_ne (show (2:Nat) ≠ 6 by omega), h2]
  have hf16arr : arrL (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2) + 1)) (11) (1)) (20) (BD2 n)) (BD2 n) (0)) (BD2 n) 1 = [0] := by
    show (List.range 1).map (fun q => (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2) + 1)) (11) (1)) (20) (BD2 n)) (BD2 n) (0)) (BD2 n + q)) = [0]
    simp only [List.range_one, List.map_cons, List.map_nil, List.cons.injEq]
    rw [Nat.add_zero]
    exact And.intro (up_eq _ _ _) True.intro
  have hpres1 : Pres (AReg2 n) f0 (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2) + 1)) (11) (1)) (20) (BD2 n)) (BD2 n) (0)) := by
    refine pres_trans (pres_up (c := 6) (v := bd1) (Or.inl (by omega))) ?_
    refine pres_trans (pres_up (c := 21) (v := 2 ^ (n / 2 + 1)) (Or.inl (by omega))) ?_
    refine pres_trans (pres_up (c := 18) (v := 3 * n + 23) (Or.inl (by omega))) ?_
    refine pres_trans (pres_up (c := 18) (v := 3 * n + 23 + 2 ^ (n / 2 + 1)) (Or.inl (by omega))) ?_
    refine pres_trans (pres_up (c := 18) (v := 3 * n + 23 + 2 ^ (n / 2 + 1) + 1) (Or.inl (by omega))) ?_
    refine pres_trans (pres_up (c := 18) (v := 3 * n + 23 + 2 ^ (n / 2 + 1) + 2) (Or.inl (by omega))) ?_
    refine pres_trans (pres_up (c := 18) (v := 3 * n + 23 + 2 ^ (n / 2 + 1) + 3) (Or.inl (by omega))) ?_
    refine pres_trans (pres_up (c := 18) (v := BD2 n) (Or.inl (by omega))) ?_
    refine pres_trans (pres_up (c := 22) (v := n - n / 2) (Or.inl (by omega))) ?_
    refine pres_trans (pres_up (c := 21) (v := 1) (Or.inl (by omega))) ?_
    refine pres_trans (pres_up (c := 21) (v := 2 ^ (n - n / 2)) (Or.inl (by omega))) ?_
    refine pres_trans (pres_up (c := 19) (v := BD2 n + 2 ^ (n - n / 2)) (Or.inl (by omega))) ?_
    refine pres_trans (pres_up (c := 19) (v := BD2 n + 2 ^ (n - n / 2) + 1) (Or.inl (by omega))) ?_
    refine pres_trans (pres_up (c := 11) (v := 1) (Or.inl (by omega))) ?_
    refine pres_trans (pres_up (c := 20) (v := BD2 n) (Or.inl (by omega))) ?_
    exact pres_up (c := BD2 n) (v := 0) (strip_in_AReg2 (n := n) (by omega) (by omega) (by omega))
  obtain ⟨f1, hf1def⟩ : ∃ g, g = up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2) + 1)) (11) (1)) (20) (BD2 n)) (BD2 n) (0) := ⟨up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (f0) (6) (bd1)) (21) (2 ^ (n / 2 + 1))) (18) (3 * n + 23)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1))) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 1)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 2)) (18) (3 * n + 23 + 2 ^ (n / 2 + 1) + 3)) (18) (BD2 n)) (22) (n - n / 2)) (21) (1)) (21) (2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2))) (19) (BD2 n + 2 ^ (n - n / 2) + 1)) (11) (1)) (20) (BD2 n)) (BD2 n) (0), rfl⟩

  -- the round loop
  have hrel1 : ∀ i, 1 ≤ i → i ≤ n - n / 2 →
      f1 (2 * n + 23 + n / 2 + i) = instA x (n / 2 + (i - 1)) := by
    intro i hi1 hi2
    have hnA : ¬ AReg2 n (2 * n + 23 + n / 2 + i) :=
      block_not_AReg2 (n := n) (by omega) (by omega) (by omega)
    rw [show n / 2 + (i - 1) = n / 2 + i - 1 from by omega]
    rw [hf1def, hpres1 _ hnA]
    have h := hrel (n / 2 + i) (by omega) (by omega)
    rw [show 2 * n + 23 + (n / 2 + i) = 2 * n + 23 + n / 2 + i from by omega] at h
    exact h
  obtain ⟨c2, f', bd2, hc2, hex2, hf210, hf211, hf218, hf2bd, hf2disj,
    hf2arr, hf21, hf22, hf27, hf28, hf26, hf29, hf2fit, hf2pres⟩ :=
    lround2_exec ρ (by omega) hw (n - n / 2 + 1) 1 1 (BD2 n)
      (BD2 n + 2 ^ (n - n / 2) + 1) f1 (S - 16) r (by omega) (by omega)
      (by rw [show (1:Nat) - 1 = 0 from rfl, Nat.pow_zero])
      (by rw [hf1def]; exact hf16_1) (by rw [hf1def]; exact hf16_2)
      (by rw [hf1def]; exact hf16_7) (by rw [hf1def]; exact hf16_8)
      (by rw [hf1def]; exact hf16_10) (by rw [hf1def]; exact hf16_11)
      (by rw [hf1def]; exact hf16_18) (by rw [hf1def]; exact hf16_19)
      (by rw [hf1def]; exact hf16arr)
      (Or.inl ⟨rfl, rfl⟩) hrel1 hin (by rw [hf1def]; exact f16fit) haddr (by omega)
      (by rw [show (1:Nat) - 1 = 0 from rfl, Nat.pow_zero]; omega)
  rw [hf1def] at hf2pres
  refine ⟨16 + c2, f', bd2, by omega, ?_, hf210, hf211, hf2bd, hf218, hf2disj,
    hf2arr, ?_, hf21, hf22, hf27, hf28, ?_, hf2fit, pres_trans hpres1 hf2pres⟩
  · rw [hf1def] at hex2
    rw [hsetup, hex2]
    rw [show S - 16 - c2 = S - (16 + c2) from by omega]
    rfl
  · rw [hf26]; rw [hf1def]; exact hf16_6
  · rw [hf29]; rw [hf1def]; exact hf16_9

/-- The PH2 budget folds to the campaign form (M6's `budget_compose2`
consumes this shape). -/
theorem phaseA2_budget (n : Nat) (hn : 2 ≤ n) :
    17 + 44 * (2 ^ (n - n / 2) - 1) + 24 * (n - n / 2) ≤ 136 * 2 ^ (n / 2) := by
  have hstep1 : 17 + 44 * (2 ^ (n - n / 2) - 1) + 24 * (n - n / 2)
      ≤ 68 * 2 ^ (n - n / 2) := by
    have hA1 : (1:Nat) ≤ 2 ^ (n - n / 2) := Nat.one_le_two_pow
    have hs := succ_le_two_pow (n - n / 2)
    omega
  have hstep2 : 68 * 2 ^ (n - n / 2) ≤ 136 * 2 ^ (n / 2) := by
    have hm : 2 ^ (n - n / 2) ≤ 2 ^ (n / 2 + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : 2 ^ (n / 2 + 1) = 2 * 2 ^ (n / 2) := by
      rw [Nat.pow_succ]; omega
    have h68 : (68:Nat) * 2 ^ (n - n / 2) ≤ 68 * 2 ^ (n / 2 + 1) :=
      Nat.mul_le_mul_left 68 hm
    omega
  calc 17 + 44 * (2 ^ (n - n / 2) - 1) + 24 * (n - n / 2)
      ≤ 68 * 2 ^ (n - n / 2) := hstep1
    _ ≤ 136 * 2 ^ (n / 2) := hstep2

end SubsetSum.MITM
