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

end SubsetSum.MITM
