import Submission.SubsetSumStatement
import Submission.Spec
import Submission.Bridge
import Submission.Sort
import Submission.Fit
import Submission.Words
import Submission.Program
import Submission.Prologue
import Submission.PhaseA
import Submission.PhaseA2
import Submission.Canon
import Submission.ScanB
import Submission.Budget
import Submission.ProgFacts
set_option autoImplicit true

/-!
# The v2 summit: prog2 discharges subset-sum at α = 1/2

End-to-end composition for the MITM rewrite `prog2` (= `prog` with phaseB
replaced by phaseA2 + canon + scanB; the instructions below pc 148 are
shared, verified by `prog2_getD_agree`).

Layout:
- `§A` the prog↔prog2 bridge primitives: `exec_peel` (shared-head one-step
  congruence), `exec_thread` (state-threading below the shared prefix),
  `prog2_getD_agree`.
- `§B` the scanB sweep-completeness lemma `scanLoop_accepts` (a pair on the
  table ⇒ the sweep accepts) — the piece `scanB_exec`'s disjunction lacks.
- `§C` `bign_run2_from148`: FROM the phaseA-exit contract at pc 148 (the
  shape `phaseA_exec` concludes), `prog2` computes the exact membership
  verdict `some (decide (isSum (instA x) n x.t))` — soundness
  (`canon_pair_iff` + `mem_halfSums` + `isSum_split`), completeness (§B),
  totality — with the 148-onward cost inside `budget_compose2`'s fold.
- `§D` the α = 1/2 runtime shape: `T n = 176·2^(n/2) + 64n` satisfies
  `T n² ≤ 61696·2ⁿ` (`budget_final`) and the `BigO` literal, plus the
  `SolvedInTime (1/2)`-shaped assembly conditioned on the 0→148 prefix
  walk (see `solved_half_of_prefix`).

RESIDUAL (precisely scoped for the next wave): the prologue+phaseA walks
(`Prologue.lean` segments, `init_exec`, `lround_exec`) are stated on `prog`.
Every instruction of `prog` below pc 148 is IDENTICAL in `prog2`
(`prog2_getD_agree`), and every internal step-pin in those proofs is a
`rfl` fact about the instruction VALUES, so the file mirrors mechanically
under prog→prog2. `§A`'s threading lemmas are the semantic reason the
mirror is sound. Until landed, `solved_half_of_prefix` carries the mirror
as an explicit hypothesis.
-/

namespace SubsetSum.MITM

open BigOSpeedrun.SubsetSum SubsetSum.MITM.Spec

set_option maxHeartbeats 12000000

/-! ## §A. The prog↔prog2 bridge primitives -/

/-- One-step congruence: if the two programs fetch the SAME instruction at
`pc` and every shorter run already agrees everywhere, the `(t+1)`-steps
agree.  This is the semantic engine of the prefix mirror. -/
theorem exec_head_congr {w : Nat} (ρ : Nat → BitVec w) {P Q : List Instr}
    {t pc r : Nat} {m : Nat → BitVec w}
    (hagree : P.getD pc .reject = Q.getD pc .reject)
    (hrec : ∀ (pc' : Nat) (r' : Nat) (m' : Nat → BitVec w),
      exec P ρ t pc' r' m' = exec Q ρ t pc' r' m') :
    exec P ρ (t + 1) pc r m = exec Q ρ (t + 1) pc r m := by
  simp only [exec]
  rw [← hagree]
  cases h : P.getD pc .reject <;>
    first | rfl | exact hrec _ _ _

set_option maxRecDepth 10000 in
/-- Bool classifier for instruction equality — `Instr` carries no
`DecidableEq`, so the agreement check below decides through this. -/
def instrBeq : Instr → Instr → Bool
  | .one i, .one j => i == j
  | .add i j k, .add i' j' k' => i == i' && j == j' && k == k'
  | .sub i j k, .sub i' j' k' => i == i' && j == j' && k == k'
  | .mul i j k, .mul i' j' k' => i == i' && j == j' && k == k'
  | .div i j k, .div i' j' k' => i == i' && j == j' && k == k'
  | .rem i j k, .rem i' j' k' => i == i' && j == j' && k == k'
  | .and i j k, .and i' j' k' => i == i' && j == j' && k == k'
  | .or i j k, .or i' j' k' => i == i' && j == j' && k == k'
  | .xor i j k, .xor i' j' k' => i == i' && j == j' && k == k'
  | .shl i j k, .shl i' j' k' => i == i' && j == j' && k == k'
  | .shr i j k, .shr i' j' k' => i == i' && j == j' && k == k'
  | .load i j, .load i' j' => i == i' && j == j'
  | .store i j, .store i' j' => i == i' && j == j'
  | .rand i, .rand i' => i == i'
  | .blt i j l, .blt i' j' l' => i == i' && j == j' && l == l'
  | .accept, .accept => true
  | .reject, .reject => true
  | _, _ => false

theorem instrBeq_eq {a b : Instr} (h : instrBeq a b = true) : a = b := by
  cases a <;> cases b <;> simp_all [instrBeq]

set_option maxRecDepth 10000 in
/-- Both programs fetch the same instruction everywhere below the phaseA2
boundary, EXCEPT pc 12 — the small-`n` dispatch `blt 0 3` targets smallN at
prog-specific 192 vs prog2-specific 253 (both fall through to 13 identically
when `n ≥ 4`, which is the only regime the v2 chain claims). -/
theorem prog2_getD_agree : ∀ pc, pc < 148 → pc ≠ 12 →
    prog2.getD pc Instr.reject = prog.getD pc Instr.reject := by
  have hall : (List.range 148).all (fun p =>
      (p == 12 || instrBeq (prog2.getD p Instr.reject) (prog.getD p Instr.reject))) = true := by
    decide
  intro pc hpc hne
  by_cases hp12 : pc = 12
  · exact absurd hp12 hne
  · have hbe : instrBeq (prog2.getD pc Instr.reject) (prog.getD pc Instr.reject) = true := by
      have hall' := List.all_eq_true.mp hall pc (List.mem_range.mpr hpc)
      simpa [hp12] using hall'
    exact instrBeq_eq hbe

/-- The peel: while the fetched instruction is shared and non-terminal,
ONE step of `P` and ONE step of `Q` land in the SAME state.  This is the
atomic step of the prefix mirror; note it needs no run-level hypothesis. -/
theorem exec_peel {w : Nat} (ρ : Nat → BitVec w) (P Q : List Instr)
    {S pc r : Nat} {m : Nat → BitVec w}
    (hagree : P.getD pc .reject = Q.getD pc .reject)
    (hS : 0 < S)
    (hnt : P.getD pc .reject ≠ .accept ∧ P.getD pc .reject ≠ .reject) :
    ∃ pc₁ : Nat, ∃ r₁ : Nat, ∃ m₁ : Nat → BitVec w,
      exec P ρ S pc r m = exec P ρ (S - 1) pc₁ r₁ m₁ ∧
      exec Q ρ S pc r m = exec Q ρ (S - 1) pc₁ r₁ m₁ := by
  obtain ⟨S', rfl⟩ : ∃ S', S = S' + 1 := ⟨S - 1, by omega⟩
  simp only [exec]
  rw [← hagree]
  cases h : P.getD pc .reject
  case accept => exact absurd h hnt.1
  case reject => exact absurd h hnt.2
  all_goals exact ⟨_, _, _, rfl, rfl⟩

/-- State-threading below the shared prefix: if every below-`B` state
agrees on ONE step (`hstep` — instantiated from `exec_peel` + instruction
agreement; pc 12's small-`n` dispatch needs the `n ≥ 4` fallthrough fact,
which is part of the prefix-mirror residual), then the `Q`-run threads the
VERY SAME states as the `P`-run for `K` steps — so any walk equation of
`P` of shift ≤ K transports verbatim to `Q`. -/
theorem exec_thread {w : Nat} (ρ : Nat → BitVec w) {P Q : List Instr} {B : Nat}
    (hstep : ∀ (S' pc r : Nat) (m : Nat → BitVec w), pc < B →
      ∃ pc₁ : Nat, ∃ r₁ : Nat, ∃ m₁ : Nat → BitVec w,
        exec P ρ (S' + 1) pc r m = exec P ρ S' pc₁ r₁ m₁ ∧
        exec Q ρ (S' + 1) pc r m = exec Q ρ S' pc₁ r₁ m₁) :
    ∀ (K S pc r : Nat) (m : Nat → BitVec w), pc < B →
      (∀ k, k ≤ K → ∀ pc₂ r₂ m₂, exec P ρ S pc r m = exec P ρ (S - k) pc₂ r₂ m₂ → pc₂ < B) →
      ∃ pcK : Nat, ∃ rK : Nat, ∃ mK : Nat → BitVec w,
        exec P ρ S pc r m = exec P ρ (S - K) pcK rK mK ∧
        exec Q ρ S pc r m = exec Q ρ (S - K) pcK rK mK := by
  intro K
  induction K with
  | zero => intro S pc r m hpc _; exact ⟨pc, r, m, rfl, rfl⟩
  | succ K ih =>
    intro S pc r m hpc hbelow
    rcases Nat.eq_zero_or_pos S with rfl | hS0
    · refine ⟨pc, r, m, ?_, ?_⟩ <;> simp
    obtain ⟨pc₁, r₁, m₁, hP₁, hQ₁⟩ := hstep (S - 1) pc r m hpc
    have hS1 : S - 1 + 1 = S := by omega
    rw [hS1] at hP₁ hQ₁
    have hpc1 : pc₁ < B := hbelow 1 (by omega) pc₁ r₁ m₁ hP₁
    have hbelow' : ∀ k, k ≤ K → ∀ pc₂ r₂ m₂,
        exec P ρ (S - 1) pc₁ r₁ m₁ = exec P ρ (S - 1 - k) pc₂ r₂ m₂ → pc₂ < B := by
      intro k hk pc₂ r₂ m₂ heq
      refine hbelow (k + 1) (by omega) pc₂ r₂ m₂ ?_
      rw [hP₁, heq, show S - 1 - k = S - (k + 1) from by omega]
    obtain ⟨pcK, rK, mK, hPK, hQK⟩ := ih (S - 1) pc₁ r₁ m₁ hpc1 hbelow'
    refine ⟨pcK, rK, mK, ?_, ?_⟩
    · rw [hP₁, hPK, show S - 1 - K = S - (K + 1) from by omega]
    · rw [hQ₁, hQK, show S - 1 - K = S - (K + 1) from by omega]

#print axioms exec_head_congr
#print axioms prog2_getD_agree
#print axioms exec_peel
#print axioms exec_thread

/-! ## §B. The scanB sweep-completeness lemma

`scanB_exec` concludes only the disjunction `some false ∨ (some true ∧
witness)`.  Completeness (a pair on the table ⇒ the sweep ACCEPTS) is the
classic two-pointer invariant: while a pair `(i', jp')` sits at-or-behind
the pointers, `A[i]+B[jp−1] < t₀` forces `i' ≥ i+1` and `> t₀` forces
`jp' ≤ jp−1` (sortedness), so the sweep cannot reject before finding it. -/

/-- The loop body's six register writes (`20, 15, 21, 16, 16`, then the
path cell `c`) never touch memory cells above the register file. -/
private theorem body6_ne {f : Nat → Nat} (v20 v15 v21 v16a v16b c vc q : Nat)
    (hq : 22 < q) (hqc : q ≠ c) :
    (up (up (up (up (up (up f 20 v20) 15 v15) 21 v21) 16 v16a) 16 v16b)
      c vc) q = f q := by
  rw [up_ne hqc, up_ne (show q ≠ 16 by omega),
    up_ne (show q ≠ 16 by omega), up_ne (show q ≠ 21 by omega),
    up_ne (show q ≠ 15 by omega), up_ne (show q ≠ 20 by omega)]

/-- Pairwise-(≤) over `(List.range L).map g` gives pointwise monotonicity
in the index — the bridge from `halfSums_sorted` to memory-cell order. -/
theorem pairwise_range_map_le {g : Nat → Nat} :
    ∀ (N : Nat), List.Pairwise (· ≤ ·) ((List.range N).map g) →
    ∀ q q', q ≤ q' → q' < N → g q ≤ g q' := by
  intro N
  induction N with
  | zero => intro _ q q' _ hq'; exact absurd hq' (by simp)
  | succ N ih =>
    intro hl q q' hqq' hq'
    have hmap : (List.range (N + 1)).map g
        = (List.range N).map g ++ [g N] := by
      rw [List.range_succ, List.map_append, List.map_singleton]
    rw [hmap, List.pairwise_append] at hl
    obtain ⟨hpre, _, hcross⟩ := hl
    rcases Nat.lt_or_ge q' N with hN' | hN'
    · exact ih hpre q q' hqq' hN'
    · have hq'N : q' = N := by omega
      rw [hq'N]
      rcases Nat.lt_or_ge q N with hN | hN
      · have hmem : g q ∈ (List.range N).map g :=
          List.mem_map.mpr ⟨q, List.mem_range.mpr hN, rfl⟩
        exact hcross (g q) hmem (g N) (by simp)
      · have hqq : q = N := by omega
        rw [hqq]
        exact Nat.le_refl _

/-- Reading the sorted array through the cells: `arrL` pairwise ⇒ cell
order at the base. -/
theorem arrL_pairwise_le {f : Nat → Nat} {b L : Nat} {l : List Nat}
    (harr : arrL f b L = l) (hl : List.Pairwise (· ≤ ·) l) :
    ∀ q q', q ≤ q' → q' < L → f (b + q) ≤ f (b + q') := by
  intro q q' hqq' hq'
  have hdef : arrL f b L = (List.range L).map (fun i => f (b + i)) := rfl
  rw [← harr, hdef] at hl
  exact pairwise_range_map_le L hl q q' hqq' hq'

/-- THE sweep-completeness lemma: with both arrays sorted ascending and a
pair `(i', jp')` at-or-behind the pointers, the sweep reaches ACCEPT. -/
theorem scanLoop_accepts {w n : Nat} (ρ : Nat → BitVec w)
    (bd1 bd2 t0 : Nat) :
    ∀ (F i jp : Nat) (f : Nat → Nat) (S r : Nat),
    22 < bd1 → 22 < bd2 →
    bd1 + 2 ^ (n / 2) ≤ bd2 + 2 ^ (n - n / 2) →
    f 1 = 1 → f 2 = 0 → f 6 = bd1 → f 12 = i → f 13 = bd2 + jp →
    f 17 = t0 → f 19 = bd2 → f 22 = 2 ^ (n / 2) →
    i < 2 ^ (n / 2) → 1 ≤ jp → jp ≤ 2 ^ (n - n / 2) →
    (∀ q, f q < 2 ^ w) →
    (∀ c, c ≤ bd2 + 2 ^ (n - n / 2) → c < 2 ^ w) →
    (∀ q, q < 2 ^ (n / 2) → ∀ q', q' < 2 ^ (n - n / 2) →
      f (bd1 + q) + f (bd2 + q') < 2 ^ w) →
    (∀ q q', q ≤ q' → q' < 2 ^ (n / 2) → f (bd1 + q) ≤ f (bd1 + q')) →
    (∀ q q', q ≤ q' → q' < 2 ^ (n - n / 2) → f (bd2 + q) ≤ f (bd2 + q')) →
    (∃ i', i ≤ i' ∧ i' < 2 ^ (n / 2) ∧
      ∃ jp', 1 ≤ jp' ∧ jp' ≤ jp ∧
        f (bd1 + i') + f (bd2 + (jp' - 1)) = t0) →
    (2 ^ (n / 2) - i) + jp ≤ F →
    10 * ((2 ^ (n / 2) - i) + jp) + 2 ≤ S →
    exec prog2 ρ S 238 r (memOf w f) = some true := by
  intro F
  induction F with
  | zero =>
    intro i jp f S r hbd1 hbd2 hb1 h1 h2 h6 h12 h13 h17 h19 h22 hilt hjp1 hjp
      hfit haddr hpair hsortedA hsortedB hfind hfuel hS
    -- measure 0 contradicts i < 2^(n/2)  (absurd, NOT exfalso: exfalso
    -- drags Classical.choice into the axioms)
    have hcon : ¬ ((2 ^ (n / 2) - i) + jp ≤ 0) := by omega
    exact absurd hfuel hcon
  | succ F ih =>
    intro i jp f S r hbd1 hbd2 hb1 h1 h2 h6 h12 h13 h17 h19 h22 hilt hjp1 hjp
      hfit haddr hpair hsortedA hsortedB ⟨i', hi'le, hi'lt, jp', hjp'1, hjp'le, hpairwit⟩
      hfuel hS
    -- the 6-step body prefix: 238 (taken, jp ≠ 0) | 240..244 → 245
    obtain ⟨S5, hS5def⟩ : ∃ g : Nat → Nat,
        g = (up (up (up (up (up f 20 (bd1 + i)) 15 (f (bd1 + i)))
          21 (bd2 + jp - 1)) 16 (f (bd2 + jp - 1)))
          16 (f (bd1 + i) + f (bd2 + (jp - 1)))) := ⟨_, rfl⟩
    have haA : 22 < bd1 + i := by omega
    have hs : f (bd1 + i) + f (bd2 + (jp - 1)) < 2 ^ w :=
      hpair i hilt (jp - 1) (by omega)
    have fitS1 : ∀ q, (up f 20 (bd1 + i)) q < 2 ^ w :=
      up_fit hfit (haddr (bd1 + i) (by omega))
    have fitS2 : ∀ q, (up (up f 20 (bd1 + i)) 15 (f (bd1 + i))) q < 2 ^ w :=
      up_fit fitS1 (hfit (bd1 + i))
    have fitS3 : ∀ q,
        (up (up (up f 20 (bd1 + i)) 15 (f (bd1 + i))) 21 (bd2 + jp - 1)) q
          < 2 ^ w := up_fit fitS2 (haddr (bd2 + jp - 1) (by omega))
    have fitS4 : ∀ q,
        (up (up (up (up f 20 (bd1 + i)) 15 (f (bd1 + i))) 21 (bd2 + jp - 1))
          16 (f (bd2 + jp - 1))) q < 2 ^ w := up_fit fitS3 (hfit (bd2 + jp - 1))
    have fitS5 : ∀ q, S5 q < 2 ^ w := by
      intro q; rw [hS5def]; exact up_fit (c := 16) fitS4 hs q
    have h17S5 : S5 17 = t0 := by
      rw [hS5def, up_ne (show (17:Nat) ≠ 16 by omega),
        up_ne (show (17:Nat) ≠ 16 by omega),
        up_ne (show (17:Nat) ≠ 21 by omega),
        up_ne (show (17:Nat) ≠ 15 by omega),
        up_ne (show (17:Nat) ≠ 20 by omega), h17]
    have h16S5 : S5 16 = f (bd1 + i) + f (bd2 + (jp - 1)) := by
      rw [hS5def, up_eq]
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
    -- the three-way decision at 245/246
    rcases Nat.lt_trichotomy (f (bd1 + i) + f (bd2 + (jp - 1))) t0 with hlt | heq | hgt
    · -- s < t₀: advance i — the pair must have i' ≥ i+1, so 251 is taken
      have hi'1 : i + 1 ≤ i' := by
        rcases Nat.lt_or_ge i' (i + 1) with hlt' | hge'
        · have hii : i' = i := by omega
          subst hii
          have hBle : f (bd2 + (jp' - 1)) ≤ f (bd2 + (jp - 1)) :=
            hsortedB (jp' - 1) (jp - 1) (by omega) (by omega)
          rw [← hpairwit] at hlt
          omega
        · exact hge'
      have hi1lt : i + 1 < 2 ^ (n / 2) := by omega
      obtain ⟨JB, hJBdef⟩ : ∃ g : Nat → Nat, g = up S5 12 (i + 1) := ⟨_, rfl⟩
      have hpowhalf : 2 ^ (n / 2) < 2 ^ w := by rw [← h22]; exact hfit 22
      have fitJB : ∀ q, JB q < 2 ^ w := by
        intro q; rw [hJBdef]
        by_cases hq12 : q = 12
        · subst hq12; rw [up_eq]; exact Nat.lt_trans hi1lt hpowhalf
        · rw [up_ne hq12]; exact fitS5 q
      have hwalk : exec prog2 ρ S 238 r (memOf w f)
          = exec prog2 ρ (S - 10) 238 r (memOf w JB) := by
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
          ← hJBdef,
          exec_blt_lt_step (S := S - 6 - 1 - 1 - 1) (by omega)
            (show prog2.getD 251 Instr.reject = Instr.blt 12 22 238 by rfl)
            fitJB (by rw [hJBdef, up_ne (show (22:Nat) ≠ 12 by omega), up_eq,
                            hS5def, up_ne (show (22:Nat) ≠ 16 by omega),
                            up_ne (show (22:Nat) ≠ 16 by omega),
                            up_ne (show (22:Nat) ≠ 21 by omega),
                            up_ne (show (22:Nat) ≠ 15 by omega),
                            up_ne (show (22:Nat) ≠ 20 by omega),
                            h22]; exact hi1lt),
          show (S - 6 - 1 - 1 - 1 - 1 : Nat) = S - 10 from by omega]
      have hAeq : ∀ q, q < 2 ^ (n / 2) → JB (bd1 + q) = f (bd1 + q) := by
        intro q hq
        rw [hJBdef, hS5def]
        exact body6_ne (bd1 + i) (f (bd1 + i)) (bd2 + jp - 1)
          (f (bd2 + jp - 1)) (f (bd1 + i) + f (bd2 + (jp - 1))) 12
          (i + 1) (bd1 + q) (by omega) (by omega)
      have hBeq : ∀ q', q' < 2 ^ (n - n / 2) → JB (bd2 + q') = f (bd2 + q') := by
        intro q' hq'
        rw [hJBdef, hS5def]
        exact body6_ne (bd1 + i) (f (bd1 + i)) (bd2 + jp - 1)
          (f (bd2 + jp - 1)) (f (bd1 + i) + f (bd2 + (jp - 1))) 12
          (i + 1) (bd2 + q') (by omega) (by omega)
      have hsortedA' : ∀ q q', q ≤ q' → q' < 2 ^ (n / 2) →
          JB (bd1 + q) ≤ JB (bd1 + q') := fun q q' hle hl =>
        by rw [hAeq q (by omega), hAeq q' hl]; exact hsortedA q q' hle hl
      have hsortedB' : ∀ q q', q ≤ q' → q' < 2 ^ (n - n / 2) →
          JB (bd2 + q) ≤ JB (bd2 + q') := fun q q' hle hl =>
        by rw [hBeq q (by omega), hBeq q' hl]; exact hsortedB q q' hle hl
      have hfind : ∃ i'', i + 1 ≤ i'' ∧ i'' < 2 ^ (n / 2) ∧
          ∃ jp'', 1 ≤ jp'' ∧ jp'' ≤ jp ∧
            JB (bd1 + i'') + JB (bd2 + (jp'' - 1)) = t0 :=
        ⟨i', by omega, hi'lt, jp', hjp'1, hjp'le, by
          rw [hAeq _ hi'lt, hBeq _ (by omega)]
          exact hpairwit⟩
      have hres := ih (i + 1) jp JB (S - 10) r hbd1 hbd2 hb1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        hi1lt hjp1 hjp fitJB haddr ?_ hsortedA' hsortedB' hfind (by omega)
        (by omega)
      rw [hwalk, hres]
      · rw [hJBdef, up_ne (show (1:Nat) ≠ 12 by omega), hS5def,
            up_ne (show (1:Nat) ≠ 16 by omega),
            up_ne (show (1:Nat) ≠ 16 by omega),
            up_ne (show (1:Nat) ≠ 21 by omega),
            up_ne (show (1:Nat) ≠ 15 by omega),
            up_ne (show (1:Nat) ≠ 20 by omega), h1]
      · rw [hJBdef, up_ne (show (2:Nat) ≠ 12 by omega), hS5def,
            up_ne (show (2:Nat) ≠ 16 by omega),
            up_ne (show (2:Nat) ≠ 16 by omega),
            up_ne (show (2:Nat) ≠ 21 by omega),
            up_ne (show (2:Nat) ≠ 15 by omega),
            up_ne (show (2:Nat) ≠ 20 by omega), h2]
      · rw [hJBdef, up_ne (show (6:Nat) ≠ 12 by omega), hS5def,
            up_ne (show (6:Nat) ≠ 16 by omega),
            up_ne (show (6:Nat) ≠ 16 by omega),
            up_ne (show (6:Nat) ≠ 21 by omega),
            up_ne (show (6:Nat) ≠ 15 by omega),
            up_ne (show (6:Nat) ≠ 20 by omega), h6]
      · rw [hJBdef, up_eq]
      · rw [hJBdef, up_ne (show (13:Nat) ≠ 12 by omega), hS5def,
            up_ne (show (13:Nat) ≠ 16 by omega),
            up_ne (show (13:Nat) ≠ 16 by omega),
            up_ne (show (13:Nat) ≠ 21 by omega),
            up_ne (show (13:Nat) ≠ 15 by omega),
            up_ne (show (13:Nat) ≠ 20 by omega), h13]
      · rw [hJBdef, up_ne (show (17:Nat) ≠ 12 by omega), hS5def,
            up_ne (show (17:Nat) ≠ 16 by omega),
            up_ne (show (17:Nat) ≠ 16 by omega),
            up_ne (show (17:Nat) ≠ 21 by omega),
            up_ne (show (17:Nat) ≠ 15 by omega),
            up_ne (show (17:Nat) ≠ 20 by omega), h17]
      · rw [hJBdef, up_ne (show (19:Nat) ≠ 12 by omega), hS5def,
            up_ne (show (19:Nat) ≠ 16 by omega),
            up_ne (show (19:Nat) ≠ 16 by omega),
            up_ne (show (19:Nat) ≠ 21 by omega),
            up_ne (show (19:Nat) ≠ 15 by omega),
            up_ne (show (19:Nat) ≠ 20 by omega), h19]
      · rw [hJBdef, up_ne (show (22:Nat) ≠ 12 by omega), hS5def,
            up_ne (show (22:Nat) ≠ 16 by omega),
            up_ne (show (22:Nat) ≠ 16 by omega),
            up_ne (show (22:Nat) ≠ 21 by omega),
            up_ne (show (22:Nat) ≠ 15 by omega),
            up_ne (show (22:Nat) ≠ 20 by omega), h22]
      · intro q hq q' hq'
        rw [hAeq q hq, hBeq q' hq']
        exact hpair q hq q' hq'
    · -- s = t₀: fall through 245 and 246 into ACCEPT — 9 steps
      rw [hprefix,
        exec_blt_ge_step (S := S - 6) (by omega)
          (show prog2.getD 245 Instr.reject = Instr.blt 17 16 248 by rfl)
          fitS5 (by rw [h17S5, h16S5]; omega),
        exec_blt_ge_step (S := S - 6 - 1) (by omega)
          (show prog2.getD 246 Instr.reject = Instr.blt 16 17 250 by rfl)
          fitS5 (by rw [h16S5, h17S5]; omega),
        exec_accept_step (S := S - 6 - 1 - 1) (by omega)
          (show prog2.getD 247 Instr.reject = Instr.accept by rfl)]
    · -- s > t₀: shrink j — the pair must have jp' ≤ jp-1
      have hjp'1' : jp' ≤ jp - 1 := by
        rcases Nat.lt_or_ge (jp - 1) jp' with hlt' | hge'
        · have hjpj : jp' = jp := by omega
          subst hjpj
          have hAle : f (bd1 + i) ≤ f (bd1 + i') := hsortedA i i' hi'le hi'lt
          rw [← hpairwit] at hgt
          omega
        · exact hge'
      obtain ⟨JB, hJBdef⟩ : ∃ g : Nat → Nat, g = up S5 13 (bd2 + jp - 1) :=
        ⟨_, rfl⟩
      have fitJB : ∀ q, JB q < 2 ^ w := by
        intro q; rw [hJBdef]
        by_cases hq13 : q = 13
        · subst hq13; rw [up_eq]; exact haddr (bd2 + jp - 1) (by omega)
        · rw [up_ne hq13]; exact fitS5 q
      have hwalk : exec prog2 ρ S 238 r (memOf w f)
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
      have hAeq : ∀ q, q < 2 ^ (n / 2) → JB (bd1 + q) = f (bd1 + q) := by
        intro q hq
        rw [hJBdef, hS5def]
        exact body6_ne (bd1 + i) (f (bd1 + i)) (bd2 + jp - 1)
          (f (bd2 + jp - 1)) (f (bd1 + i) + f (bd2 + (jp - 1))) 13
          (bd2 + jp - 1) (bd1 + q) (by omega) (by omega)
      have hBeq : ∀ q', q' < 2 ^ (n - n / 2) → JB (bd2 + q') = f (bd2 + q') := by
        intro q' hq'
        rw [hJBdef, hS5def]
        exact body6_ne (bd1 + i) (f (bd1 + i)) (bd2 + jp - 1)
          (f (bd2 + jp - 1)) (f (bd1 + i) + f (bd2 + (jp - 1))) 13
          (bd2 + jp - 1) (bd2 + q') (by omega) (by omega)
      have hfind : ∃ i'', i ≤ i'' ∧ i'' < 2 ^ (n / 2) ∧
          ∃ jp'', 1 ≤ jp'' ∧ jp'' ≤ jp - 1 ∧
            JB (bd1 + i'') + JB (bd2 + (jp'' - 1)) = t0 :=
        ⟨i', hi'le, hi'lt, jp', hjp'1, by omega, by
          rw [hAeq _ hi'lt, hBeq _ (by omega)]
          exact hpairwit⟩
      have hsortedA' : ∀ q q', q ≤ q' → q' < 2 ^ (n / 2) →
          JB (bd1 + q) ≤ JB (bd1 + q') := fun q q' hle hl =>
        by rw [hAeq q (by omega), hAeq q' hl]; exact hsortedA q q' hle hl
      have hsortedB' : ∀ q q', q ≤ q' → q' < 2 ^ (n - n / 2) →
          JB (bd2 + q) ≤ JB (bd2 + q') := fun q q' hle hl =>
        by rw [hBeq q (by omega), hBeq q' hl]; exact hsortedB q q' hle hl
      have hres := ih i (jp - 1) JB (S - 9) r hbd1 hbd2 hb1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        hilt (by omega) (by omega) fitJB haddr ?_ hsortedA' hsortedB' hfind
        (by omega) (by omega)
      rw [hwalk, hres]
      · rw [hJBdef, up_ne (show (1:Nat) ≠ 13 by omega), hS5def,
          up_ne (show (1:Nat) ≠ 16 by omega),
          up_ne (show (1:Nat) ≠ 16 by omega),
          up_ne (show (1:Nat) ≠ 21 by omega),
          up_ne (show (1:Nat) ≠ 15 by omega),
          up_ne (show (1:Nat) ≠ 20 by omega), h1]
      · rw [hJBdef, up_ne (show (2:Nat) ≠ 13 by omega), hS5def,
          up_ne (show (2:Nat) ≠ 16 by omega),
          up_ne (show (2:Nat) ≠ 16 by omega),
          up_ne (show (2:Nat) ≠ 21 by omega),
          up_ne (show (2:Nat) ≠ 15 by omega),
          up_ne (show (2:Nat) ≠ 20 by omega), h2]
      · rw [hJBdef, up_ne (show (6:Nat) ≠ 13 by omega), hS5def,
          up_ne (show (6:Nat) ≠ 16 by omega),
          up_ne (show (6:Nat) ≠ 16 by omega),
          up_ne (show (6:Nat) ≠ 21 by omega),
          up_ne (show (6:Nat) ≠ 15 by omega),
          up_ne (show (6:Nat) ≠ 20 by omega), h6]
      · rw [hJBdef, up_ne (show (12:Nat) ≠ 13 by omega), hS5def,
          up_ne (show (12:Nat) ≠ 16 by omega),
          up_ne (show (12:Nat) ≠ 16 by omega),
          up_ne (show (12:Nat) ≠ 21 by omega),
          up_ne (show (12:Nat) ≠ 15 by omega),
          up_ne (show (12:Nat) ≠ 20 by omega), h12]
      · rw [hJBdef, up_eq]
        omega
      · rw [hJBdef, up_ne (show (17:Nat) ≠ 13 by omega), hS5def,
          up_ne (show (17:Nat) ≠ 16 by omega),
          up_ne (show (17:Nat) ≠ 16 by omega),
          up_ne (show (17:Nat) ≠ 21 by omega),
          up_ne (show (17:Nat) ≠ 15 by omega),
          up_ne (show (17:Nat) ≠ 20 by omega), h17]
      · rw [hJBdef, up_ne (show (19:Nat) ≠ 13 by omega), hS5def,
          up_ne (show (19:Nat) ≠ 16 by omega),
          up_ne (show (19:Nat) ≠ 16 by omega),
          up_ne (show (19:Nat) ≠ 21 by omega),
          up_ne (show (19:Nat) ≠ 15 by omega),
          up_ne (show (19:Nat) ≠ 20 by omega), h19]
      · rw [hJBdef, up_ne (show (22:Nat) ≠ 13 by omega), hS5def,
          up_ne (show (22:Nat) ≠ 16 by omega),
          up_ne (show (22:Nat) ≠ 16 by omega),
          up_ne (show (22:Nat) ≠ 21 by omega),
          up_ne (show (22:Nat) ≠ 15 by omega),
          up_ne (show (22:Nat) ≠ 20 by omega), h22]
      · intro q hq q' hq'
        rw [hAeq q hq, hBeq q' hq']
        exact hpair q hq q' hq'


/-! ## §C. The from-148 discharge -/

/-- Subset sums of `k` values each `≤ bound` are `≤ k * bound`. -/
theorem choiceSum_le {a : Nat → Nat} {S : Nat → Bool} {k bound : Nat}
    (hb : ∀ i, i < k → (if S i then a i else 0) ≤ bound) :
    choiceSum a S k ≤ k * bound := by
  unfold choiceSum
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton]
    have hIH := ih (fun i hi => hb i (by omega))
    have hk := hb k (by omega)
    have hsplit : (k + 1) * bound = k * bound + bound := by
      rw [Nat.add_mul, Nat.one_mul]
    omega

/-- scanB's 7-step setup (pcs 231→238): straight-line register writes, no
branches.  Exports the loop-entry pins `scanLoop_accepts` consumes. -/
theorem scanB_setup7 {w n : Nat} (ρ : Nat → BitVec w)
    (bd1 bd2 t0 : Nat) (f : Nat → Nat) (r S : Nat)
    (hbd2 : 22 < bd2)
    (h1 : f 1 = 1) (h2 : f 2 = 0) (h6 : f 6 = bd1) (h7 : f 7 = n)
    (h8 : f 8 = 2 * n + 23) (h9 : f 9 = n / 2)
    (h11 : f 11 = 2 ^ (n - n / 2)) (h19 : f 19 = bd2)
    (ht0 : f (3 * n + 24) = t0)
    (hfit : ∀ q, f q < 2 ^ w)
    (hb2 : bd2 + 2 ^ (n - n / 2) ≤ BD2 n + 2 * 2 ^ (n - n / 2) + 1)
    (haddr : ∀ c, c ≤ BD2 n + 2 * 2 ^ (n - n / 2) + 1 → c < 2 ^ w)
    (hS : 7 ≤ S) :
    ∃ g : Nat → Nat,
      exec prog2 ρ S 231 r (memOf w f) = exec prog2 ρ (S - 7) 238 r (memOf w g) ∧
      g 1 = 1 ∧ g 2 = 0 ∧ g 6 = bd1 ∧ g 12 = 0 ∧
      g 13 = bd2 + 2 ^ (n - n / 2) ∧ g 17 = t0 ∧ g 19 = bd2 ∧
      g 22 = 2 ^ (n / 2) ∧ g (3 * n + 24) = t0 ∧ g 7 = n ∧ g 8 = 2 * n + 23 ∧
      g 9 = n / 2 ∧ g 11 = 2 ^ (n - n / 2) ∧
      (∀ q, 22 < q → g q = f q) ∧
      (∀ q, g q < 2 ^ w) ∧
      (∀ c, c ≤ bd2 + 2 ^ (n - n / 2) → c < 2 ^ w) := by
  have hBD : BD2 n = 3 * n + 25 + 2 * 2 ^ (n / 2) + 2 := rfl
  have hpowHalf : 2 ^ (n / 2) ≤ 2 ^ (n - n / 2) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h0lt : (0:Nat) < 2 ^ w := Nat.one_le_two_pow (n := w)
  have h1lt : (1:Nat) < 2 ^ w := by
    rw [← h1]; exact hfit 1
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
    have hb : 2 ^ (n / 2) ≤ BD2 n + 2 * 2 ^ (n - n / 2) + 1 := by
      rw [hBD]; omega
    exact Nat.lt_of_le_of_lt hb (haddr _ (Nat.le_refl _))
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
          (memOf w (up (up (up (up (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2)))
            20 (3 * n + 23)) 20 (3 * n + 24)) 17 t0) 22 1) 22
            ((up (up (up (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2)))
              20 (3 * n + 23)) 20 (3 * n + 24)) 17 t0) 22 1) 22
              * 2 ^ (up (up (up (up (up (up f 12 0) 13 (bd2 + 2 ^ (n - n / 2)))
                20 (3 * n + 23)) 20 (3 * n + 24)) 17 t0) 22 1) 9))) :=
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
      n236, e237, n237, ← hG7def]
  refine ⟨G7, hsetup, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [hG7def, up_ne (show (1:Nat) ≠ 22 by omega),
      up_ne (show (1:Nat) ≠ 22 by omega),
      up_ne (show (1:Nat) ≠ 17 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 20 by omega),
      up_ne (show (1:Nat) ≠ 13 by omega),
      up_ne (show (1:Nat) ≠ 12 by omega), h1]
  · rw [hG7def, up_ne (show (2:Nat) ≠ 22 by omega),
      up_ne (show (2:Nat) ≠ 22 by omega),
      up_ne (show (2:Nat) ≠ 17 by omega),
      up_ne (show (2:Nat) ≠ 20 by omega),
      up_ne (show (2:Nat) ≠ 20 by omega),
      up_ne (show (2:Nat) ≠ 13 by omega),
      up_ne (show (2:Nat) ≠ 12 by omega), h2]
  · rw [hG7def, up_ne (show (6:Nat) ≠ 22 by omega),
      up_ne (show (6:Nat) ≠ 22 by omega),
      up_ne (show (6:Nat) ≠ 17 by omega),
      up_ne (show (6:Nat) ≠ 20 by omega),
      up_ne (show (6:Nat) ≠ 20 by omega),
      up_ne (show (6:Nat) ≠ 13 by omega),
      up_ne (show (6:Nat) ≠ 12 by omega), h6]
  · rw [hG7def, up_ne (show (12:Nat) ≠ 22 by omega),
      up_ne (show (12:Nat) ≠ 22 by omega),
      up_ne (show (12:Nat) ≠ 17 by omega),
      up_ne (show (12:Nat) ≠ 20 by omega),
      up_ne (show (12:Nat) ≠ 20 by omega),
      up_ne (show (12:Nat) ≠ 13 by omega), up_eq]
  · rw [hG7def, up_ne (show (13:Nat) ≠ 22 by omega),
      up_ne (show (13:Nat) ≠ 22 by omega),
      up_ne (show (13:Nat) ≠ 17 by omega),
      up_ne (show (13:Nat) ≠ 20 by omega),
      up_ne (show (13:Nat) ≠ 20 by omega), up_eq]
  · rw [hG7def, up_ne (show (17:Nat) ≠ 22 by omega),
      up_ne (show (17:Nat) ≠ 22 by omega), up_eq]
  · rw [hG7def, up_ne (show (19:Nat) ≠ 22 by omega),
      up_ne (show (19:Nat) ≠ 22 by omega),
      up_ne (show (19:Nat) ≠ 17 by omega),
      up_ne (show (19:Nat) ≠ 20 by omega),
      up_ne (show (19:Nat) ≠ 20 by omega),
      up_ne (show (19:Nat) ≠ 13 by omega),
      up_ne (show (19:Nat) ≠ 12 by omega), h19]
  · rw [hG7def, up_eq]
  · rw [hG7def, up_ne (show (3 * n + 24 : Nat) ≠ 22 by omega),
      up_ne (show (3 * n + 24 : Nat) ≠ 22 by omega),
      up_ne (show (3 * n + 24 : Nat) ≠ 17 by omega),
      up_ne (show (3 * n + 24 : Nat) ≠ 20 by omega),
      up_ne (show (3 * n + 24 : Nat) ≠ 20 by omega),
      up_ne (show (3 * n + 24 : Nat) ≠ 13 by omega),
      up_ne (show (3 * n + 24 : Nat) ≠ 12 by omega), ht0]
  · rw [hG7def, up_ne (show (7:Nat) ≠ 22 by omega),
      up_ne (show (7:Nat) ≠ 22 by omega),
      up_ne (show (7:Nat) ≠ 17 by omega),
      up_ne (show (7:Nat) ≠ 20 by omega),
      up_ne (show (7:Nat) ≠ 20 by omega),
      up_ne (show (7:Nat) ≠ 13 by omega),
      up_ne (show (7:Nat) ≠ 12 by omega), h7]
  · rw [hG7def, up_ne (show (8:Nat) ≠ 22 by omega),
      up_ne (show (8:Nat) ≠ 22 by omega),
      up_ne (show (8:Nat) ≠ 17 by omega),
      up_ne (show (8:Nat) ≠ 20 by omega),
      up_ne (show (8:Nat) ≠ 20 by omega),
      up_ne (show (8:Nat) ≠ 13 by omega),
      up_ne (show (8:Nat) ≠ 12 by omega), h8]
  · rw [hG7def, up_ne (show (9:Nat) ≠ 22 by omega),
      up_ne (show (9:Nat) ≠ 22 by omega),
      up_ne (show (9:Nat) ≠ 17 by omega),
      up_ne (show (9:Nat) ≠ 20 by omega),
      up_ne (show (9:Nat) ≠ 20 by omega),
      up_ne (show (9:Nat) ≠ 13 by omega),
      up_ne (show (9:Nat) ≠ 12 by omega), h9]
  · rw [hG7def, up_ne (show (11:Nat) ≠ 22 by omega),
      up_ne (show (11:Nat) ≠ 22 by omega),
      up_ne (show (11:Nat) ≠ 17 by omega),
      up_ne (show (11:Nat) ≠ 20 by omega),
      up_ne (show (11:Nat) ≠ 20 by omega),
      up_ne (show (11:Nat) ≠ 13 by omega),
      up_ne (show (11:Nat) ≠ 12 by omega), h11]
  · intro q hq
    rw [hG7def, up_ne (show q ≠ 22 by omega),
      up_ne (show q ≠ 22 by omega),
      up_ne (show q ≠ 17 by omega),
      up_ne (show q ≠ 20 by omega),
      up_ne (show q ≠ 20 by omega),
      up_ne (show q ≠ 13 by omega),
      up_ne (show q ≠ 12 by omega)]
  · intro q
    have hq := fit7 q
    rw [hG7def] at hq
    rw [hG7def]
    exact hq
  · intro c hc
    have hbe : bd2 ≤ BD2 n + 2 * 2 ^ (n - n / 2) + 1 := by have := hb2; omega
    by_cases h12c : c = 12
    · subst h12c
      exact Nat.lt_of_le_of_lt (by omega) (haddr _ hbe)
    by_cases h13c : c = 13
    · subst h13c
      exact Nat.lt_of_le_of_lt (by omega) (haddr _ hbe)
    by_cases h20c : c = 20
    · subst h20c
      exact Nat.lt_of_le_of_lt (by omega) (haddr _ hbe)
    by_cases h17c : c = 17
    · subst h17c
      exact Nat.lt_of_le_of_lt (by omega) (haddr _ hbe)
    by_cases h22c : c = 22
    · subst h22c
      exact Nat.lt_of_le_of_lt (by omega) (haddr _ hbe)
    · exact haddr c (Nat.le_trans hc hb2)


@[simp] theorem arrL_length {f : Nat → Nat} {b L : Nat} :
    (arrL f b L).length = L := by
  unfold arrL; simp

/-- Value at index: `arrL` is the range-map of the cell reads. -/
theorem arrL_val {f : Nat → Nat} {b L q : Nat} (hq : q < L) :
    (arrL f b L)[q]? = some (f (b + q)) := by
  unfold arrL arrAt
  rw [List.getElem?_map, List.getElem?_range]
  all_goals simp [hq]

/-- `instA` at an in-bounds index is the Fin-array read (the dite does not
reduce under `exact`'s defeq when the instance is stuck). -/
theorem instA_in_lt {n : Nat} (x : Instance n) {i : Nat} (hi : i < n) :
    instA x i = x.a ⟨i, hi⟩ := by
  simp only [instA]
  exact dif_pos hi

/-! ### §C2. THE from-148 discharge

The phaseA-exit contract (the shape `phaseA_exec` concludes, supplied here
as hypotheses) plus the word-length envelope gives the EXACT membership
verdict: soundness via `canon_pair_iff` + `mem_halfSums`, completeness via
`isSum_split` + `scanLoop_accepts`. -/

theorem arrL_mem {f : Nat → Nat} {b L q : Nat} (hq : q < L) :
    f (b + q) ∈ arrL f b L := by
  unfold arrL
  exact List.mem_map_of_mem (List.mem_range.mpr hq)

theorem arrL_mem_pos {f : Nat → Nat} {b L s : Nat}
    (hmem : s ∈ arrL f b L) :
    ∃ q, q < L ∧ f (b + q) = s := by
  unfold arrL at hmem
  obtain ⟨q, hq, hs⟩ := List.mem_map.mp hmem
  exact ⟨q, List.mem_range.mp hq, hs⟩

theorem clamp_le_succ (t0 v : Nat) : clamp t0 v ≤ t0 + 1 := by
  unfold clamp
  split <;> omega

/-- Soundness of a sweep witness (membership form): a first-half sum `v`
plus a second-half sum `s` equal to `t₀` gives the subset-sum
decomposition.  Canon's clamp is undone at the call site via
`canon_pair_iff`. -/
theorem isSum_of_witness {n : Nat} {x : Instance n} {t0 : Nat}
    {v s : Nat}
    (hwit : v + s = t0)
    (hmemA : v ∈ halfSums (instA x) (n / 2))
    (hmemB : s ∈ halfSums (fun i => instA x (n / 2 + i)) (n - n / 2)) :
    isSum (instA x) n t0 := by
  have hisA : isSum (instA x) (n / 2) v :=
    (mem_halfSums _ _ _).mp hmemA
  have hisB : isSum (fun i => instA x (n / 2 + i)) (n - n / 2) s :=
    (mem_halfSums _ _ _).mp hmemB
  have hv : v ≤ t0 := by omega
  have hisB' : isSum (fun i => instA x (i + n / 2)) (n - n / 2)
      (t0 - v) := by
    rw [show t0 - v = s from by omega]
    have hcomm : (fun i => instA x (i + n / 2))
        = (fun i => instA x (n / 2 + i)) := by
      funext i; rw [Nat.add_comm]
    rw [hcomm]
    exact hisB
  have hfinal := (isSum_split (instA x) (n / 2) (n - n / 2) t0).mpr
    ⟨v, hv, hisA, hisB'⟩
  have hnn : n / 2 + (n - n / 2) = n := by omega
  rw [hnn] at hfinal
  exact hfinal

/-- Position of a half-sum in the A-array: the clamped cell holds it. -/
theorem exists_clamped_pos {n : Nat} {x : Instance n} {bd1 : Nat}
    {f' f'' : Nat → Nat} {s : Nat} {t0 : Nat}
    (hA : arrL f' bd1 (2 ^ (n / 2)) = halfSums (instA x) (n / 2))
    (hmap : arrL f'' bd1 (2 ^ (n / 2))
      = (arrL f' bd1 (2 ^ (n / 2))).map (clamp t0))
    (hmem : s ∈ halfSums (instA x) (n / 2)) :
    ∃ q, q < 2 ^ (n / 2) ∧ f'' (bd1 + q) = clamp t0 s := by
  have h2 : s ∈ arrL f' bd1 (2 ^ (n / 2)) := by rw [hA]; exact hmem
  have h1 : clamp t0 s ∈ arrL f'' bd1 (2 ^ (n / 2)) := by
    rw [hmap]; exact List.mem_map_of_mem h2
  exact arrL_mem_pos h1

/-- Position of a second-half sum in the B-array. -/
theorem exists_B_pos {n : Nat} {x : Instance n} {bd2 : Nat} {f' : Nat → Nat}
    {s : Nat}
    (hB : arrL f' bd2 (2 ^ (n - n / 2))
      = halfSums (fun i => instA x (n / 2 + i)) (n - n / 2))
    (hmem : s ∈ halfSums (fun i => instA x (n / 2 + i)) (n - n / 2)) :
    ∃ q, q < 2 ^ (n - n / 2) ∧ f' (bd2 + q) = s := by
  have h1 : s ∈ arrL f' bd2 (2 ^ (n - n / 2)) := by rw [hB]; exact hmem
  exact arrL_mem_pos h1


open scoped Classical in
/-- THE from-148 discharge: from the phaseA-exit contract (the shape
`phaseA_exec` concludes) the v2 program computes the EXACT membership
verdict.  Soundness: a sweep witness transports through canon's clamp
(`canon_pair_iff`) and both half-array memberships (`mem_halfSums`) to the
subset-sum decomposition.  Completeness: the decomposition positions both
half-sums inside the sweep's unexplored window, so `scanLoop_accepts`
forces ACCEPT. -/
theorem bign_run2_from148 {w n : Nat} (ρ : Nat → BitVec w) {x : Instance n}
    (hn : 4 ≤ n) (hw : wordLength n x.bits ≤ w)
    (f0 : Nat → Nat) (bd1 t0 : Nat) (r S : Nat)
    (hfit : ∀ q, f0 q < 2 ^ w)
    (h1 : f0 1 = 1) (h2 : f0 2 = 0) (h7 : f0 7 = n) (h8 : f0 8 = 2 * n + 23)
    (h9 : f0 9 = n / 2) (h10 : f0 10 = n / 2 + 1)
    (h18 : f0 18 = bd1) (h6 : f0 6 = bd1)
    (hb1 : bd1 = 3 * n + 25 ∨ bd1 = 3 * n + 25 + 2 ^ (n / 2) + 1)
    (harr : arrL f0 bd1 (2 ^ (n / 2)) = halfSums (instA x) (n / 2))
    (ht0 : f0 (3 * n + 24) = t0) (ht0v : t0 = x.t)
    (haddr : ∀ c, c ≤ BD2 n + 2 * 2 ^ (n - n / 2) + 1 → c < 2 ^ w)
    (hrel : ∀ i, 1 ≤ i → i ≤ n → f0 (2 * n + 23 + i) = instA x (i - 1))
    (hin : ∀ i, i < n → instA x i < 2 ^ w)
    (hS : 176 * 2 ^ (n / 2) + 64 * n ≤ S) :
    exec prog2 ρ S 148 r (memOf w f0) = some (decide (isSum (instA x) n x.t)) := by
  have hBD : BD2 n = 3 * n + 25 + 2 * 2 ^ (n / 2) + 2 := rfl
  have h0lt : (0:Nat) < 2 ^ w := Nat.one_le_two_pow (n := w)
  have hw1 : 1 ≤ w := by
    have hw' := hw
    unfold wordLength at hw'
    have : 0 ≤ Nat.log2 ((n + 2) ^ 4 - 1) := Nat.zero_le _
    omega
  have hpownnz : 0 ≤ 2 ^ (n / 2) - 1 := by
    have := Nat.one_le_two_pow (n := n / 2)
    omega
  have hpownnz2 : 0 ≤ 2 ^ (n - n / 2) - 1 := by
    have := Nat.one_le_two_pow (n := n - n / 2)
    omega
  have hpow2 : 2 ^ (n - n / 2) ≤ 2 * 2 ^ (n / 2) := by
    have h1 : 2 ^ (n - n / 2) ≤ 2 ^ (n / 2 + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.pow_succ] at h1
    omega
  have hbits : x.bits < w := by
    have hw' := hw
    unfold wordLength at hw'
    have h1 : x.bits ≤ 4 * (n + x.bits) := by omega
    have h2 : 0 ≤ Nat.log2 ((n + 2) ^ 4 - 1) := Nat.zero_le _
    omega
  have hmax : x.maxValue < 2 ^ x.bits := maxValue_lt_pow x (by omega)
  have ht0le : t0 ≤ x.maxValue := ht0v ▸ maxValue_ge_t x
  have ht0lt : t0 < 2 ^ x.bits := Nat.lt_of_le_of_lt ht0le hmax
  have ht0fit : t0 + 1 < 2 ^ w := by
    have h1 : t0 + 1 ≤ 2 ^ x.bits := by omega
    have h2 : 2 ^ x.bits < 2 ^ w :=
      Nat.pow_lt_pow_right (by omega) hbits
    omega
  -- phase A2: 148 -> 215
  obtain ⟨c₂, f', bd2, hc₂, hex₂, hf'10, hf'11, hf'19, hf'18, hbd2disj,
    hf'arr, hf'6, hf'1, hf'2, hf'7, hf'8, hf'9, hf'fit, hf'pres⟩ :=
    phaseA2_exec ρ hn hw f0 r S hfit h1 h2 h7 h8 h9 h10 h18 hb1 harr haddr
      hrel hin (by omega)
  -- the t-cell carries through phaseA2 (3n+24 outside AReg2), and the
  -- budget fold ties the three phase fuels to T = 176*2^(n/2)+64n
  have hpresT : f' (3 * n + 24) = t0 := by
    have hnA : ¬ AReg2 n (3 * n + 24) := by
      intro hA
      rcases hA with hA | ⟨hA, _⟩ <;> omega
    rw [hf'pres _ hnA]
    exact ht0
  have hbc := budget_compose2 (n := n) hn
  have hBnn1 : 0 ≤ 12 + 44 * (2 ^ (n / 2) - 1) + 24 * (n / 2) := by
    have := Nat.one_le_two_pow (n := n / 2)
    omega
  have hBnn2 : 0 ≤ 44 * (2 ^ (n - n / 2) - 1) := by
    have := Nat.one_le_two_pow (n := n - n / 2)
    omega
  -- canon: 215 -> 231 (clamps the first half in place; M7 pass-throughs)
  obtain ⟨c₃, f'', hc₃, hex₃, hf''arr, hf''6, hf''1, hf''2, hf''7, hf''8,
    hf''9, hf''11, hf''12, hf''13, hf''17, hf''19, hf''fit, hf''pres⟩ :=
    canon_exec ρ f' bd1 t0 r (S - c₂)
      (by rcases hb1 with rfl | rfl <;> omega)
      (by have := hb1; omega)
      hf'fit hw1 hf'1 hf'2 hf'7 hf'8 hf'9 hf'6 hf'11
      (by have hnA : ¬ AReg2 n (3 * n + 24) := by
            intro hA
            rcases hA with hA | ⟨hA, _⟩ <;> omega
          rw [hf'pres _ hnA]
          exact ht0)
      ht0fit haddr (by omega)
  have hpresT'' : f'' (3 * n + 24) = t0 := by
    have hnA : ¬ ARegC n bd1 (3 * n + 24) := by
      intro hA
      rcases hA with hA | ⟨hA, _⟩ <;> omega
    rw [hf''pres _ hnA]
    exact hpresT
  -- the pre-canon A-array (A-cells sit outside AReg2 for n ≥ 4, so Pres
  -- transports `harr` from f0 to f'): hsortedA's sortedness source
  have hf'arrA : arrL f' bd1 (2 ^ (n / 2)) = halfSums (instA x) (n / 2) := by
    have hpre : ∀ q, q < 2 ^ (n / 2) → f' (bd1 + q) = f0 (bd1 + q) := by
      intro q hq
      have hnA : ¬ AReg2 n (bd1 + q) := by
        intro hA
        rcases hA with hA | ⟨hA, _⟩ <;>
          rcases hb1 with rfl | rfl <;> omega
      exact hf'pres _ hnA
    have he : arrL f' bd1 (2 ^ (n / 2))
        = (List.range (2 ^ (n / 2))).map (fun q => f0 (bd1 + q)) := by
      rw [show arrL f' bd1 (2 ^ (n / 2))
          = (List.range (2 ^ (n / 2))).map (fun q => f' (bd1 + q)) from rfl]
      exact List.map_congr_left fun q hq => hpre q (List.mem_range.mp hq)
    rw [he, show (List.range (2 ^ (n / 2))).map (fun q => f0 (bd1 + q))
        = arrL f0 bd1 (2 ^ (n / 2)) from rfl, harr]
  -- fuel facts from budget_compose2's fold (isolated so the (by omega)s
  -- below see a small context)
  have hfuelA : 7 * 2 ^ (n / 2) + 9 ≤ S - c₂ := by omega
  have hfuel : 10 * (2 ^ (n / 2) + 2 ^ (n - n / 2)) + 9 ≤ S - c₂ - c₃ := by
    omega
  -- canon exports 19 in preservation form; setup7/scanB_exec want the pin
  have hf''19bd2 : f'' 19 = bd2 := by
    rw [hf''19]
    exact hf'19
  -- scanB envelope facts
  have hbd2lt : 22 < bd2 := by
    rcases hbd2disj with rfl | rfl <;>
      rw [hBD] <;>
      have h4 : (2:Nat) ^ 2 ≤ 2 ^ (n / 2) :=
        Nat.pow_le_pow_right (by omega) (by omega) <;> omega
  have hb1' : bd1 + 2 ^ (n / 2) ≤ bd2 + 2 ^ (n - n / 2) := by
    rcases hb1 with rfl | rfl
    · rcases hbd2disj with rfl | rfl <;> omega
    · rcases hbd2disj with rfl | rfl <;> omega
  have hb2' : bd2 + 2 ^ (n - n / 2) ≤ BD2 n + 2 * 2 ^ (n - n / 2) + 1 := by
    rcases hbd2disj with rfl | rfl <;> omega
  -- the pair envelope on the canon-exit state
  have hpresAB : ∀ q, q < 2 ^ (n / 2) →
      f'' (bd1 + q) = clamp t0 (f' (bd1 + q)) := by
    intro q hq
    have h1 : (arrL f'' bd1 (2 ^ (n / 2)))[q]? = some (f'' (bd1 + q)) :=
      arrL_val hq
    rw [hf''arr, List.getElem?_map, arrL_val hq] at h1
    simpa using h1.symm
  have hpresB : ∀ q, q < 2 ^ (n - n / 2) → f'' (bd2 + q) = f' (bd2 + q) := by
    intro q hq
    have hnA : ¬ ARegC n bd1 (bd2 + q) := by
      intro hA
      rcases hA with hA | ⟨hA, _⟩ <;> omega
    rw [hf''pres _ hnA]
  have hpair'' : ∀ q, q < 2 ^ (n / 2) → ∀ q', q' < 2 ^ (n - n / 2) →
      f'' (bd1 + q) + f'' (bd2 + q') < 2 ^ w := by
    intro q hq q' hq'
    have hvA := clamp_le_succ t0 (f' (bd1 + q))
    rw [← hpresAB q hq] at hvA
    have hmem : f' (bd2 + q') ∈ halfSums (fun i => instA x (n / 2 + i))
        (n - n / 2) := by
      have h1 := arrL_mem (f := f') (b := bd2) (L := 2 ^ (n - n / 2)) hq'
      rw [hf'arr] at h1
      exact h1
    have hisB := (mem_halfSums _ _ _).mp hmem
    obtain ⟨S, hSn, hsum⟩ := hisB
    have hbound : choiceSum (fun i => instA x (n / 2 + i)) S (n - n / 2)
        ≤ (n - n / 2) * x.maxValue :=
      choiceSum_le (fun i hi => by
        by_cases hSi : S i = true
        · rw [if_pos hSi]
          rw [instA_in_lt x (by omega)]
          exact maxValue_ge_a x ⟨n / 2 + i, by omega⟩
        · rw [if_neg hSi]
          omega)
    -- the maxValue roof: keep the product terms syntactic (omega cannot
    -- relate (n-n/2)·mV to n·mV — atomized via the add_mul split)
    have hvB : f' (bd2 + q') ≤ n * x.maxValue := by
      have hbound2 : f' (bd2 + q') ≤ (n - n / 2) * x.maxValue := by
        rw [← hsum]
        exact hbound
      have hsplit : n * x.maxValue
          = (n / 2) * x.maxValue + (n - n / 2) * x.maxValue := by
        rw [← Nat.add_mul]
        congr 1
        omega
      rw [hsplit]
      exact Nat.le_trans hbound2 (Nat.le_add_left _ _)
    rw [hpresB q' hq']
    exact pair_sum_lt_two_pow x (by omega) w hw (f'' (bd1 + q))
      (f' (bd2 + q')) t0 hvA hvB ht0le
  -- the sweep, entered at (0, 2^(n-n/2))
  obtain ⟨g, hsetup, hg1, hg2, hg6, hg12, hg13, hg17, hg19, hg22,
    hgT, hg7, hg8, hg9, hg11, hgcellpres, hgfit, hgaddr⟩ :=
    scanB_setup7 ρ bd1 bd2 t0 f'' r (S - c₂ - c₃) hbd2lt hf''1 hf''2 hf''6
      hf''7 hf''8 hf''9 hf''11 hf''19bd2 hpresT'' hf''fit hb2' haddr
      (by omega)
  -- sortedness of both arrays on the loop-entry state
  have hcellpres : ∀ q, 22 < q → g q = f'' q := hgcellpres
  have hpresB'arr : arrL f'' bd2 (2 ^ (n - n / 2))
      = halfSums (fun i => instA x (n / 2 + i)) (n - n / 2) := by
    rw [show arrL f'' bd2 (2 ^ (n - n / 2))
        = (List.range (2 ^ (n - n / 2))).map (fun q => f'' (bd2 + q)) from rfl,
      List.map_congr_left (fun q hq => hpresB q (List.mem_range.mp hq)),
      show (List.range (2 ^ (n - n / 2))).map (fun q => f' (bd2 + q))
        = arrL f' bd2 (2 ^ (n - n / 2)) from rfl,
      hf'arr]
  have hsortedA : ∀ q q', q ≤ q' → q' < 2 ^ (n / 2) →
      g (bd1 + q) ≤ g (bd1 + q') := by
    intro q q' hle hlt
    have hP : List.Pairwise (· ≤ ·)
        ((List.range (2 ^ (n / 2))).map (fun q => f'' (bd1 + q))) := by
      have he : (List.range (2 ^ (n / 2))).map (fun q => f'' (bd1 + q))
          = (halfSums (instA x) (n / 2)).map (clamp t0) := by
        rw [show (List.range (2 ^ (n / 2))).map (fun q => f'' (bd1 + q))
          = arrL f'' bd1 (2 ^ (n / 2)) from rfl, hf''arr, hf'arrA]
      rw [he]
      exact canon_sorted_map (halfSums_sorted (instA x) (n / 2))
    have hraw := pairwise_range_map_le _ hP q q' hle hlt
    rw [hcellpres (bd1 + q) (by omega), hcellpres (bd1 + q') (by omega)]
    exact hraw
  have hsortedB : ∀ q q', q ≤ q' → q' < 2 ^ (n - n / 2) →
      g (bd2 + q) ≤ g (bd2 + q') := by
    intro q q' hle hlt
    have hP : List.Pairwise (· ≤ ·)
        ((List.range (2 ^ (n - n / 2))).map (fun q => f'' (bd2 + q))) := by
      have he : (List.range (2 ^ (n - n / 2))).map (fun q => f'' (bd2 + q))
          = halfSums (fun i => instA x (n / 2 + i)) (n - n / 2) := by
        rw [show (List.range (2 ^ (n - n / 2))).map (fun q => f'' (bd2 + q))
          = arrL f'' bd2 (2 ^ (n - n / 2)) from rfl, hpresB'arr]
      rw [he]
      exact halfSums_sorted (fun i => instA x (n / 2 + i)) (n - n / 2)
    have hraw := pairwise_range_map_le _ hP q q' hle hlt
    rw [hcellpres (bd2 + q) (by omega), hcellpres (bd2 + q') (by omega)]
    exact hraw
  by_cases his : isSum (instA x) n x.t
  · -- completeness: the decomposition places both sums in the window
    have his' : isSum (instA x) (n / 2 + (n - n / 2)) x.t := by
      rw [show n / 2 + (n - n / 2) = n from by omega]
      exact his
    obtain ⟨s, hsle, hisA, hisB⟩ :=
      (isSum_split (instA x) (n / 2) (n - n / 2) x.t).mp his'
    have hmemA : s ∈ halfSums (instA x) (n / 2) :=
      (mem_halfSums _ _ _).mpr hisA
    have hcomm : (fun i => instA x (i + n / 2))
        = (fun i => instA x (n / 2 + i)) := by
      funext i; rw [Nat.add_comm]
    have hmemB : (x.t - s) ∈ halfSums (fun i => instA x (n / 2 + i))
        (n - n / 2) := by
      rw [hcomm] at hisB
      exact (mem_halfSums _ _ _).mpr hisB
    obtain ⟨q₁, hq₁, hcell₁⟩ := exists_clamped_pos hf'arrA hf''arr hmemA
    obtain ⟨q₂, hq₂, hcell₂⟩ := exists_B_pos hf'arr hmemB
    have hfind : ∃ i', 0 ≤ i' ∧ i' < 2 ^ (n / 2) ∧
        ∃ jp', 1 ≤ jp' ∧ jp' ≤ 2 ^ (n - n / 2) ∧
          g (bd1 + i') + g (bd2 + (jp' - 1)) = t0 :=
      ⟨q₁, by omega, hq₁, q₂ + 1, by omega, by omega, by
        rw [hgcellpres (bd1 + q₁) (by omega),
          hgcellpres (bd2 + (q₂ + 1 - 1)) (by omega),
          hcell₁, show q₂ + 1 - 1 = q₂ from by omega,
          hpresB q₂ (by omega), hcell₂]
        -- clamp t0 s + (x.t - s) = t0  via  canon_pair_iff  and  s + (x.t - s) = x.t
        exact (canon_pair_iff (t0 := t0) (v := s) (s := x.t - s)).mpr (by omega)⟩
    have hloop := scanLoop_accepts ρ bd1 bd2 t0
      (2 ^ (n / 2) + 2 ^ (n - n / 2)) 0 (2 ^ (n - n / 2)) g (S - c₂ - c₃ - 7) r
      (by rcases hb1 with rfl | rfl <;> omega) hbd2lt hb1' hg1 hg2 hg6 hg12
      hg13 hg17 hg19 hg22 (by omega) (by omega) (by omega) hgfit hgaddr
      (fun q hq q' hq' => by
        rw [hgcellpres (bd1 + q) (by omega),
          hgcellpres (bd2 + q') (by omega)]
        exact hpair'' q hq q' hq')
      hsortedA hsortedB hfind (by omega) (by omega)
    -- chain the three walks (hex₂ ends at pcCanon, hex₃ at pcScanB)
    have hex : exec prog2 ρ S 148 r (memOf w f0) = some true := by
      rw [hex₂, show pcCanon = 215 from rfl, hex₃, show pcScanB = 231 from rfl,
        hsetup, hloop]
    rw [hex]
    congr 1
    exact (decide_eq_true_iff.mpr his).symm
  · -- soundness: a true verdict would carry a witness back to isSum
    obtain ⟨c₄, hc₄, hex₄⟩ :=
      scanB_exec ρ f'' bd1 bd2 t0 r (S - c₂ - c₃)
        (by rcases hb1 with rfl | rfl <;> omega) hbd2lt hb1' hb2' hw1
        hf''fit hf''1 hf''2 hf''6 hf''7 hf''8 hf''9 hf''11 hf''19bd2 hpresT''
        haddr hpair'' hfuel
    rcases hex₄ with hfalse | ⟨htrue, i', jp', hi', hj1', hjN', hwit⟩
    · -- the sweep rejected: the verdict register reads false
      have hd : decide (isSum (instA x) n x.t) = false :=
        decide_eq_false_iff_not.mpr his
      rw [hex₂, show pcCanon = 215 from rfl, hex₃, show pcScanB = 231 from rfl,
        hfalse, hd]
    · exfalso
      -- un-clamp the A-cell: canon's clamp is verdict-preserving
      obtain ⟨v, hvmem, hveq⟩ : ∃ v, v ∈ halfSums (instA x) (n / 2) ∧
          clamp t0 v = f'' (bd1 + i') := by
        have hmem1 : f'' (bd1 + i') ∈ arrL f'' bd1 (2 ^ (n / 2)) := arrL_mem hi'
        rw [hf''arr] at hmem1
        obtain ⟨v, hv, hveq⟩ := List.mem_map.mp hmem1
        refine ⟨v, ?_, hveq⟩
        rw [hf'arrA] at hv
        exact hv
      have hjplt : jp' - 1 < 2 ^ (n - n / 2) := by omega
      have hmem₂ : f'' (bd2 + (jp' - 1))
          ∈ halfSums (fun i => instA x (n / 2 + i)) (n - n / 2) := by
        rw [hpresB (jp' - 1) hjplt]
        have h1 := arrL_mem (f := f') (b := bd2)
          (L := 2 ^ (n - n / 2)) (q := jp' - 1) hjplt
        rw [hf'arr] at h1
        exact h1
      have hwit' : v + f'' (bd2 + (jp' - 1)) = t0 := by
        have h1 : clamp t0 v + f'' (bd2 + (jp' - 1)) = t0 := by
          rw [hveq]; exact hwit
        exact (canon_pair_iff (t0 := t0) (v := v)
          (s := f'' (bd2 + (jp' - 1)))).mp h1
      have his' : isSum (instA x) n x.t := by
        rw [← ht0v]
        exact isSum_of_witness (n := n) (x := x) (t0 := t0) hwit' hvmem hmem₂
      exact his his'
#print axioms scanLoop_accepts
#print axioms scanB_setup7
#print axioms choiceSum_le
#print axioms bign_run2_from148

end SubsetSum.MITM
