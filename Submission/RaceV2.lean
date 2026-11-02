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

#print axioms scanLoop_accepts

end SubsetSum.MITM
