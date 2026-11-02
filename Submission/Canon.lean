import Submission.PhaseA2
set_option autoImplicit true

/-!
# Canon: v2 canonicalization (M4) + the M1 array obligations

`canon` (`Program.lean`, pcs 215..230) clamps the first-half array at
`bd1` in place: entries above `t₀` (the relocated target, memory cell
`3n+24`) become `t₀+1`.  M1-decided semantics, encoded as-is.

§1 `clamp` + the M1 obligations:
   - `clamp_mono` / `canon_sorted_map` — clamping keeps the array sorted;
   - `canon_pair_iff` — a clamped entry pairs to `t₀` iff the original
     does (entries above `t₀` can never participate: every element is
     nonnegative, so `t₀+1 + s > t₀`).
§2 `ARegC n bd1` — canon's write region (registers ≤ 22 plus the strip).
§3 `canonLoop_exec` — one fuel-driven walk of the loop `222 → 222`.
§4 `canon_exec` — the phase walk `215 → 231` with the TRUE step budget
   `7 * 2^(n/2) + 9` (7 setup + 7 per element + 2 exit; the encoded loop
   body is 7 instructions per element, not the gap map's ≤ 6 sketch).
-/

namespace SubsetSum.MITM

open BigOSpeedrun.SubsetSum SubsetSum.MITM.Spec

/-! ## §1. The clamp and the M1 obligations -/

/-- canon's clamp: keep entries at or below `t₀`, raise the rest to
`t₀ + 1` (M1-decided semantics). -/
def clamp (t0 v : Nat) : Nat := if v ≤ t0 then v else t0 + 1

theorem clamp_of_le {t0 v : Nat} (h : v ≤ t0) : clamp t0 v = v := by
  unfold clamp
  rw [if_pos h]

theorem clamp_of_gt {t0 v : Nat} (h : t0 < v) : clamp t0 v = t0 + 1 := by
  unfold clamp
  rw [if_neg (by omega)]

/-- M1 (a): clamping is monotone non-decreasing. -/
theorem clamp_mono {t0 v v' : Nat} (h : v ≤ v') : clamp t0 v ≤ clamp t0 v' := by
  unfold clamp
  split <;> split <;> omega

/-- M1 (a): the clamped array is still sorted (house form:
`List.Pairwise (· ≤ ·)`, cf. `halfSums_sorted`). -/
theorem canon_sorted_map {t0 : Nat} {l : List Nat}
    (hs : List.Pairwise (· ≤ ·) l) :
    List.Pairwise (· ≤ ·) (l.map (clamp t0)) :=
  hs.map (clamp t0) (fun _ _ hab => clamp_mono hab)

/-- M1 (b): verdict preservation, pointwise.  For a B-side summand `s`
(any `s : Nat`, in particular every second-half subset sum), the clamped
first-half entry `clamp t₀ v` pairs with `s` to `t₀` iff `v` does. -/
theorem canon_pair_iff {t0 v s : Nat} : clamp t0 v + s = t0 ↔ v + s = t0 := by
  unfold clamp
  split
  · exact Iff.rfl
  · constructor
    · intro h
      omega
    · intro h
      omega

/-! ## §2. canon's write region -/

/-- canon writes the register file (cells ≤ 22) and the first-half strip
`[bd1, bd1 + 2^(n/2))`.  Everything else — the relocated input block, the
`t` cell `3n+24`, and the second-half strip — is preserved. -/
def ARegC (n bd1 : Nat) (c : Nat) : Prop :=
  c ≤ 22 ∨ bd1 ≤ c ∧ c < bd1 + 2 ^ (n / 2)

/-! ## §3. The canon loop (pcs 222 → 222, 7 steps per element) -/

/-- Fuel-driven walk of canon's loop: entered at `LCN` (pc 222) with `i`
elements already clamped, exits at pc 231 (`LCNDONE` = `pcScanB`) with the
whole strip clamped. -/
theorem canonLoop_exec {w n : Nat} (ρ : Nat → BitVec w)
    (f0 : Nat → Nat) (bd1 t0 : Nat) :
    ∀ (F i : Nat) (f : Nat → Nat) (S r : Nat),
    22 < bd1 →
    f 1 = 1 → f 2 = 0 → f 7 = n → f 8 = 2 * n + 23 → f 9 = n / 2 →
    f 6 = bd1 → f 11 = 2 ^ (n - n / 2) →
    f 21 = 2 ^ (n / 2) → f 16 = t0 → f 22 = t0 + 1 → f 14 = i →
    i ≤ 2 ^ (n / 2) →
    (∀ q, f0 q < 2 ^ w) →
    (∀ q, f q < 2 ^ w) →
    (∀ c, c ≤ bd1 + 2 ^ (n / 2) → c < 2 ^ w) →
    (∀ q, q < i → f (bd1 + q) = clamp t0 (f0 (bd1 + q))) →
    (∀ q, i ≤ q → q < 2 ^ (n / 2) → f (bd1 + q) = f0 (bd1 + q)) →
    Pres (ARegC n bd1) f0 f →
    2 ^ (n / 2) - i ≤ F →
    7 * (2 ^ (n / 2) - i) + 2 ≤ S →
    ∃ c f', c ≤ 7 * (2 ^ (n / 2) - i) + 2 ∧
      exec prog2 ρ S 222 r (memOf w f) = exec prog2 ρ (S - c) 231 r (memOf w f') ∧
      f' 14 = 2 ^ (n / 2) ∧ f' 21 = 2 ^ (n / 2) ∧ f' 16 = t0 ∧ f' 22 = t0 + 1 ∧
      f' 6 = bd1 ∧ f' 1 = 1 ∧ f' 2 = 0 ∧ f' 7 = n ∧ f' 8 = 2 * n + 23 ∧
      f' 9 = n / 2 ∧ f' 11 = 2 ^ (n - n / 2) ∧
      (∀ q, f' q < 2 ^ w) ∧
      (∀ q, q < 2 ^ (n / 2) → f' (bd1 + q) = clamp t0 (f0 (bd1 + q))) ∧
      Pres (ARegC n bd1) f0 f' := by
  intro F
  induction F with
  | zero =>
    intro i f S r hbd1 h1 h2 h7 h8 h9 h6 h11 h21 h16 h22 h14 hiN hfit0 hfit
      haddrC hB hC hpres hfuel hS
    -- fuel exhausted: i = 2^(n/2); take the exit branch (222 → 223 → 231)
    have hiEq : i = 2 ^ (n / 2) := by omega
    subst hiEq
    have hgeExit : ¬ f 14 < f 21 := by rw [h14, h21]; omega
    have hltJ : f 2 < f 1 := by rw [h2, h1]; omega
    refine ⟨2, f, by omega, ?_, h14, h21, h16, h22, h6, h1, h2,
      h7, h8, h9, h11, hfit, hB, hpres⟩
    rw [exec_blt_ge_step (S := S) (by omega)
      (show prog2.getD 222 Instr.reject = Instr.blt 14 21 224 by rfl) hfit
      hgeExit,
      exec_blt_lt_step (S := S - 1) (by omega)
      (show prog2.getD 223 Instr.reject = Instr.blt 2 1 231 by rfl) hfit
      hltJ]
    simp only [Nat.sub_sub]
  | succ F ih =>
    intro i f S r hbd1 h1 h2 h7 h8 h9 h6 h11 h21 h16 h22 h14 hiN hfit0 hfit
      haddrC hB hC hpres hfuel hS
    rcases Nat.lt_or_ge i (2 ^ (n / 2)) with hilt | hiEq
    · -- one iteration: 222 | 224 | 225 | 226 | 227/228 | 229 | 230, 7 steps
      have h0lt : (0:Nat) < 2 ^ w := Nat.one_le_two_pow (n := w)
      have hG : (0:Nat) ≤ i := Nat.zero_le _
      have fit1 : ∀ q, (up f 20 (bd1 + i)) q < 2 ^ w :=
        up_fit hfit (haddrC (bd1 + i) (by omega))
      rcases Nat.lt_or_ge t0 (f0 (bd1 + i)) with hv | hv
      · -- clamp path: 226 taken, the cell is stored as t0 + 1
        have fit2 : ∀ q,
            (up (up f 20 (bd1 + i)) 15 (f0 (bd1 + i))) q < 2 ^ w :=
          up_fit fit1 (hfit0 (bd1 + i))
        have hNfit : 2 ^ (n / 2) < 2 ^ w := haddrC (2 ^ (n / 2)) (by omega)
        have hfitStore : t0 + 1 < 2 ^ w := by rw [← h22]; exact hfit 22
        have hlt222 : f 14 < f 21 := by rw [h14, h21]; exact hilt
        have hlt226 : (up (up f 20 (bd1 + i)) 15 (f0 (bd1 + i))) 16
            < (up (up f 20 (bd1 + i)) 15 (f0 (bd1 + i))) 15 := by
          rw [up_ne (show (16:Nat) ≠ 15 by omega),
              up_ne (show (16:Nat) ≠ 20 by omega), h16, up_eq]
          exact hv
        have hlt230 : (up (up (up (up f 20 (bd1 + i)) 15 (f0 (bd1 + i)))
              (bd1 + i) (t0 + 1)) 14 (i + 1)) 2
            < (up (up (up (up f 20 (bd1 + i)) 15 (f0 (bd1 + i)))
              (bd1 + i) (t0 + 1)) 14 (i + 1)) 1 := by
          rw [up_ne (show (2:Nat) ≠ 14 by omega),
              up_ne (show (2:Nat) ≠ (bd1:Nat) + i by omega),
              up_ne (show (2:Nat) ≠ 15 by omega),
              up_ne (show (2:Nat) ≠ 20 by omega), h2,
              up_ne (show (1:Nat) ≠ 14 by omega),
              up_ne (show (1:Nat) ≠ (bd1:Nat) + i by omega),
              up_ne (show (1:Nat) ≠ 15 by omega),
              up_ne (show (1:Nat) ≠ 20 by omega), h1]
          omega
        have hfitNext : ∀ q,
            (up (up (up (up f 20 (bd1 + i)) 15 (f0 (bd1 + i))) (bd1 + i)
              (t0 + 1)) 14 (i + 1)) q < 2 ^ w :=
          up_fit (up_fit fit2 hfitStore) (by omega)
        have hbody : exec prog2 ρ S 222 r (memOf w f)
            = exec prog2 ρ (S - 7) 222 r
                (memOf w (up (up (up (up f 20 (bd1 + i)) 15 (f0 (bd1 + i)))
                  (bd1 + i) (t0 + 1)) 14 (i + 1))) := by
          rw [exec_blt_lt_step (S := S) (by omega)
              (show prog2.getD 222 Instr.reject = Instr.blt 14 21 224 by rfl) hfit
              hlt222,
            exec_add_step (S := S - 1) (by omega)
              (show prog2.getD 224 Instr.reject = Instr.add 20 6 14 by rfl),
            show (up f 20 (f 6 + f 14)) = up f 20 (bd1 + i) from by
              rw [h6, h14],
            exec_load_step (S := S - 1 - 1) (by omega)
              (show prog2.getD (224 + 1) Instr.reject = Instr.load 15 20 by rfl) fit1,
            up_eq,
            up_ne (show ((bd1:Nat) + i) ≠ 20 by omega),
            hC i (by omega) (by omega),
            exec_blt_lt_step (S := S - 1 - 1 - 1) (by omega)
              (show prog2.getD (224 + 1 + 1) Instr.reject = Instr.blt 16 15 228 by rfl) fit2
              hlt226,
            exec_store_step (S := S - 1 - 1 - 1 - 1) (by omega)
              (show prog2.getD 228 Instr.reject = Instr.store 20 22 by rfl) fit2,
            show (up (up f 20 (bd1 + i)) 15 (f0 (bd1 + i))) 20 = bd1 + i from by
              rw [up_ne (show (20:Nat) ≠ 15 by omega), up_eq],
            show (up (up f 20 (bd1 + i)) 15 (f0 (bd1 + i))) 22 = t0 + 1 from by
              rw [up_ne (show (22:Nat) ≠ 15 by omega),
                  up_ne (show (22:Nat) ≠ 20 by omega), h22],
            exec_add_step (S := S - 1 - 1 - 1 - 1 - 1) (by omega)
              (show prog2.getD 229 Instr.reject = Instr.add 14 14 1 by rfl),
            show (up (up (up f 20 (bd1 + i)) 15 (f0 (bd1 + i))) (bd1 + i)
                (t0 + 1)) 14 + (up (up (up f 20 (bd1 + i)) 15 (f0 (bd1 + i)))
                (bd1 + i) (t0 + 1)) 1 = i + 1 from by
              rw [up_ne (show (14:Nat) ≠ (bd1:Nat) + i by omega),
                  up_ne (show (14:Nat) ≠ 15 by omega),
                  up_ne (show (14:Nat) ≠ 20 by omega), h14,
                  up_ne (show (1:Nat) ≠ (bd1:Nat) + i by omega),
                  up_ne (show (1:Nat) ≠ 15 by omega),
                  up_ne (show (1:Nat) ≠ 20 by omega), h1],
            exec_blt_lt_step (S := S - 1 - 1 - 1 - 1 - 1 - 1) (by omega)
              (show prog2.getD (228 + 1 + 1) Instr.reject = Instr.blt 2 1 222 by rfl)
              hfitNext
              hlt230]
          simp only [Nat.sub_sub]
        -- recurse from the post-iteration state
        obtain ⟨c', f', hc', hex, h14', h21', h16', h22', h6', h1', h2', h7',
          h8', h9', h11', hfit', hB', hpres'⟩ :=
          ih (i + 1)
            (up (up (up (up f 20 (bd1 + i)) 15 (f0 (bd1 + i))) (bd1 + i)
              (t0 + 1)) 14 (i + 1)) (S - 7) r hbd1
            (by rw [up_ne (show (1:Nat) ≠ 14 by omega),
                    up_ne (show (1:Nat) ≠ (bd1:Nat) + i by omega),
                    up_ne (show (1:Nat) ≠ 15 by omega),
                    up_ne (show (1:Nat) ≠ 20 by omega), h1])
            (by rw [up_ne (show (2:Nat) ≠ 14 by omega),
                    up_ne (show (2:Nat) ≠ (bd1:Nat) + i by omega),
                    up_ne (show (2:Nat) ≠ 15 by omega),
                    up_ne (show (2:Nat) ≠ 20 by omega), h2])
            (by rw [up_ne (show (7:Nat) ≠ 14 by omega),
                    up_ne (show (7:Nat) ≠ (bd1:Nat) + i by omega),
                    up_ne (show (7:Nat) ≠ 15 by omega),
                    up_ne (show (7:Nat) ≠ 20 by omega), h7])
            (by rw [up_ne (show (8:Nat) ≠ 14 by omega),
                    up_ne (show (8:Nat) ≠ (bd1:Nat) + i by omega),
                    up_ne (show (8:Nat) ≠ 15 by omega),
                    up_ne (show (8:Nat) ≠ 20 by omega), h8])
            (by rw [up_ne (show (9:Nat) ≠ 14 by omega),
                    up_ne (show (9:Nat) ≠ (bd1:Nat) + i by omega),
                    up_ne (show (9:Nat) ≠ 15 by omega),
                    up_ne (show (9:Nat) ≠ 20 by omega), h9])
            (by rw [up_ne (show (6:Nat) ≠ 14 by omega),
                    up_ne (show (6:Nat) ≠ (bd1:Nat) + i by omega),
                    up_ne (show (6:Nat) ≠ 15 by omega),
                    up_ne (show (6:Nat) ≠ 20 by omega), h6])
            (by rw [up_ne (show (11:Nat) ≠ 14 by omega),
                    up_ne (show (11:Nat) ≠ (bd1:Nat) + i by omega),
                    up_ne (show (11:Nat) ≠ 15 by omega),
                    up_ne (show (11:Nat) ≠ 20 by omega), h11])
            (by rw [up_ne (show (21:Nat) ≠ 14 by omega),
                    up_ne (show (21:Nat) ≠ (bd1:Nat) + i by omega),
                    up_ne (show (21:Nat) ≠ 15 by omega),
                    up_ne (show (21:Nat) ≠ 20 by omega), h21])
            (by rw [up_ne (show (16:Nat) ≠ 14 by omega),
                    up_ne (show (16:Nat) ≠ (bd1:Nat) + i by omega),
                    up_ne (show (16:Nat) ≠ 15 by omega),
                    up_ne (show (16:Nat) ≠ 20 by omega), h16])
            (by rw [up_ne (show (22:Nat) ≠ 14 by omega),
                    up_ne (show (22:Nat) ≠ (bd1:Nat) + i by omega),
                    up_ne (show (22:Nat) ≠ 15 by omega),
                    up_ne (show (22:Nat) ≠ 20 by omega), h22])
            (by rw [up_eq])
            (by omega) hfit0
            hfitNext
            haddrC
            (by intro q hq
                rcases Nat.lt_or_ge q i with hq' | hq'
                · rw [up_ne (show (bd1:Nat) + q ≠ 14 by omega),
                      up_ne (show (bd1:Nat) + q ≠ (bd1:Nat) + i by omega),
                      up_ne (show (bd1:Nat) + q ≠ 15 by omega),
                      up_ne (show (bd1:Nat) + q ≠ 20 by omega)]
                  exact hB q hq'
                · have hqi : q = i := by omega
                  rw [hqi]
                  rw [up_ne (show (bd1:Nat) + i ≠ 14 by omega), up_eq]
                  rw [clamp_of_gt hv])
            (by intro q hq1 hq2
                rw [up_ne (show (bd1:Nat) + q ≠ 14 by omega),
                    up_ne (show (bd1:Nat) + q ≠ (bd1:Nat) + i by omega),
                    up_ne (show (bd1:Nat) + q ≠ 15 by omega),
                    up_ne (show (bd1:Nat) + q ≠ 20 by omega)]
                exact hC q (by omega) hq2)
            (pres_trans hpres (pres_trans (pres_up (c := 20)
              (show ARegC n bd1 20 from Or.inl (by omega)))
              (pres_trans (pres_up (c := 15)
                (show ARegC n bd1 15 from Or.inl (by omega)))
              (pres_trans (pres_up (c := bd1 + i)
                (show ARegC n bd1 (bd1 + i) from Or.inr ⟨by omega, by omega⟩))
              (pres_up (c := 14) (show ARegC n bd1 14 from Or.inl (by omega)))))))
            (by omega) (by omega)
        refine ⟨7 + c', f', by omega, ?_, h14', h21', h16', h22', h6', h1',
          h2', h7', h8', h9', h11', hfit', hB', hpres'⟩
        rw [hbody, hex, show S - 7 - c' = S - (7 + c') from by omega]
      · -- keep path: 226 falls through to 227 (`jmp LCNN`), cell untouched
        have fit2 : ∀ q,
            (up (up f 20 (bd1 + i)) 15 (f0 (bd1 + i))) q < 2 ^ w :=
          up_fit fit1 (hfit0 (bd1 + i))
        have hNfit : 2 ^ (n / 2) < 2 ^ w := haddrC (2 ^ (n / 2)) (by omega)
        have hge226 : ¬ (up (up f 20 (bd1 + i)) 15 (f0 (bd1 + i))) 16
            < (up (up f 20 (bd1 + i)) 15 (f0 (bd1 + i))) 15 := by
          rw [up_ne (show (16:Nat) ≠ 15 by omega),
              up_ne (show (16:Nat) ≠ 20 by omega), h16, up_eq]
          omega
        have hlt227 : (up (up f 20 (bd1 + i)) 15 (f0 (bd1 + i))) 2
            < (up (up f 20 (bd1 + i)) 15 (f0 (bd1 + i))) 1 := by
          rw [up_ne (show (2:Nat) ≠ 15 by omega),
              up_ne (show (2:Nat) ≠ 20 by omega), h2,
              up_ne (show (1:Nat) ≠ 15 by omega),
              up_ne (show (1:Nat) ≠ 20 by omega), h1]
          omega
        have hlt230 : (up (up (up f 20 (bd1 + i)) 15 (f0 (bd1 + i))) 14
              (i + 1)) 2
            < (up (up (up f 20 (bd1 + i)) 15 (f0 (bd1 + i))) 14 (i + 1)) 1 := by
          rw [up_ne (show (2:Nat) ≠ 14 by omega),
              up_ne (show (2:Nat) ≠ 15 by omega),
              up_ne (show (2:Nat) ≠ 20 by omega), h2,
              up_ne (show (1:Nat) ≠ 14 by omega),
              up_ne (show (1:Nat) ≠ 15 by omega),
              up_ne (show (1:Nat) ≠ 20 by omega), h1]
          omega
        have hfitNext : ∀ q,
            (up (up (up f 20 (bd1 + i)) 15 (f0 (bd1 + i))) 14 (i + 1)) q < 2 ^ w :=
          up_fit fit2 (by omega)
        have hlt222 : f 14 < f 21 := by rw [h14, h21]; exact hilt
        have hbody : exec prog2 ρ S 222 r (memOf w f)
            = exec prog2 ρ (S - 7) 222 r
                (memOf w (up (up (up f 20 (bd1 + i)) 15 (f0 (bd1 + i))) 14
                  (i + 1))) := by
          rw [exec_blt_lt_step (S := S) (by omega)
              (show prog2.getD 222 Instr.reject = Instr.blt 14 21 224 by rfl) hfit
              hlt222,
            exec_add_step (S := S - 1) (by omega)
              (show prog2.getD 224 Instr.reject = Instr.add 20 6 14 by rfl),
            show (up f 20 (f 6 + f 14)) = up f 20 (bd1 + i) from by
              rw [h6, h14],
            exec_load_step (S := S - 1 - 1) (by omega)
              (show prog2.getD (224 + 1) Instr.reject = Instr.load 15 20 by rfl) fit1,
            up_eq,
            up_ne (show ((bd1:Nat) + i) ≠ 20 by omega),
            hC i (by omega) (by omega),
            exec_blt_ge_step (S := S - 1 - 1 - 1) (by omega)
              (show prog2.getD (224 + 1 + 1) Instr.reject = Instr.blt 16 15 228 by rfl) fit2
              hge226,
            exec_blt_lt_step (S := S - 1 - 1 - 1 - 1) (by omega)
              (show prog2.getD (226 + 1) Instr.reject = Instr.blt 2 1 229 by rfl) fit2
              hlt227,
            exec_add_step (S := S - 1 - 1 - 1 - 1 - 1) (by omega)
              (show prog2.getD 229 Instr.reject = Instr.add 14 14 1 by rfl),
            show (up (up f 20 (bd1 + i)) 15 (f0 (bd1 + i))) 14
                + (up (up f 20 (bd1 + i)) 15 (f0 (bd1 + i))) 1 = i + 1 from by
              rw [up_ne (show (14:Nat) ≠ 15 by omega),
                  up_ne (show (14:Nat) ≠ 20 by omega), h14,
                  up_ne (show (1:Nat) ≠ 15 by omega),
                  up_ne (show (1:Nat) ≠ 20 by omega), h1],
            exec_blt_lt_step (S := S - 1 - 1 - 1 - 1 - 1 - 1) (by omega)
              (show prog2.getD (229 + 1) Instr.reject = Instr.blt 2 1 222 by rfl)
              hfitNext
              hlt230]
          simp only [Nat.sub_sub]
        obtain ⟨c', f', hc', hex, h14', h21', h16', h22', h6', h1', h2', h7',
          h8', h9', h11', hfit', hB', hpres'⟩ :=
          ih (i + 1)
            (up (up (up f 20 (bd1 + i)) 15 (f0 (bd1 + i))) 14 (i + 1)) (S - 7) r
            hbd1
            (by rw [up_ne (show (1:Nat) ≠ 14 by omega),
                    up_ne (show (1:Nat) ≠ 15 by omega),
                    up_ne (show (1:Nat) ≠ 20 by omega), h1])
            (by rw [up_ne (show (2:Nat) ≠ 14 by omega),
                    up_ne (show (2:Nat) ≠ 15 by omega),
                    up_ne (show (2:Nat) ≠ 20 by omega), h2])
            (by rw [up_ne (show (7:Nat) ≠ 14 by omega),
                    up_ne (show (7:Nat) ≠ 15 by omega),
                    up_ne (show (7:Nat) ≠ 20 by omega), h7])
            (by rw [up_ne (show (8:Nat) ≠ 14 by omega),
                    up_ne (show (8:Nat) ≠ 15 by omega),
                    up_ne (show (8:Nat) ≠ 20 by omega), h8])
            (by rw [up_ne (show (9:Nat) ≠ 14 by omega),
                    up_ne (show (9:Nat) ≠ 15 by omega),
                    up_ne (show (9:Nat) ≠ 20 by omega), h9])
            (by rw [up_ne (show (6:Nat) ≠ 14 by omega),
                    up_ne (show (6:Nat) ≠ 15 by omega),
                    up_ne (show (6:Nat) ≠ 20 by omega), h6])
            (by rw [up_ne (show (11:Nat) ≠ 14 by omega),
                    up_ne (show (11:Nat) ≠ 15 by omega),
                    up_ne (show (11:Nat) ≠ 20 by omega), h11])
            (by rw [up_ne (show (21:Nat) ≠ 14 by omega),
                    up_ne (show (21:Nat) ≠ 15 by omega),
                    up_ne (show (21:Nat) ≠ 20 by omega), h21])
            (by rw [up_ne (show (16:Nat) ≠ 14 by omega),
                    up_ne (show (16:Nat) ≠ 15 by omega),
                    up_ne (show (16:Nat) ≠ 20 by omega), h16])
            (by rw [up_ne (show (22:Nat) ≠ 14 by omega),
                    up_ne (show (22:Nat) ≠ 15 by omega),
                    up_ne (show (22:Nat) ≠ 20 by omega), h22])
            (by rw [up_eq])
            (by omega) hfit0 hfitNext
            haddrC
            (by intro q hq
                rcases Nat.lt_or_ge q i with hq' | hq'
                · rw [up_ne (show (bd1:Nat) + q ≠ 14 by omega),
                      up_ne (show (bd1:Nat) + q ≠ 15 by omega),
                      up_ne (show (bd1:Nat) + q ≠ 20 by omega)]
                  exact hB q hq'
                · have hqi : q = i := by omega
                  rw [hqi]
                  rw [up_ne (show (bd1:Nat) + i ≠ 14 by omega),
                      up_ne (show (bd1:Nat) + i ≠ 15 by omega),
                      up_ne (show (bd1:Nat) + i ≠ 20 by omega),
                      hC i (by omega) (by omega),
                      clamp_of_le (by omega)])
            (by intro q hq1 hq2
                rw [up_ne (show (bd1:Nat) + q ≠ 14 by omega),
                    up_ne (show (bd1:Nat) + q ≠ 15 by omega),
                    up_ne (show (bd1:Nat) + q ≠ 20 by omega)]
                exact hC q (by omega) hq2)
            (pres_trans hpres (pres_trans (pres_up (c := 20)
              (show ARegC n bd1 20 from Or.inl (by omega)))
              (pres_trans (pres_up (c := 15)
                (show ARegC n bd1 15 from Or.inl (by omega)))
              (pres_up (c := 14) (show ARegC n bd1 14 from Or.inl (by omega))))))
            (by omega) (by omega)
        refine ⟨7 + c', f', by omega, ?_, h14', h21', h16', h22', h6', h1',
          h2', h7', h8', h9', h11', hfit', hB', hpres'⟩
        rw [hbody, hex, show S - 7 - c' = S - (7 + c') from by omega]
    · -- already done: exit branch (222 → 223 → 231), 2 steps
      have hiEq : i = 2 ^ (n / 2) := by omega
      subst hiEq
      have hgeExit : ¬ f 14 < f 21 := by rw [h14, h21]; omega
      have hltJ : f 2 < f 1 := by rw [h2, h1]; omega
      refine ⟨2, f, by omega, ?_, h14, h21, h16, h22, h6, h1, h2,
        h7, h8, h9, h11, hfit, hB, hpres⟩
      rw [exec_blt_ge_step (S := S) (by omega)
        (show prog2.getD 222 Instr.reject = Instr.blt 14 21 224 by rfl) hfit
        hgeExit,
          exec_blt_lt_step (S := S - 1) (by omega)
        (show prog2.getD 223 Instr.reject = Instr.blt 2 1 231 by rfl) hfit
        hltJ]
      simp only [Nat.sub_sub]

/-! ## §4. The phase driver (pc 215 → 231) -/

/-- M4: running `prog2`'s `canon` segment from pc 215 clamps the
first-half array at `bd1` in place and reaches `pcScanB` with the TRUE
budget `7 * 2^(n/2) + 9`.  The write region is `ARegC n bd1`, so the
relocated input block, the `t` cell and the second-half strip all
survive for `scanB`. -/
theorem canon_exec {w n : Nat} (ρ : Nat → BitVec w)
    (f0 : Nat → Nat) (bd1 t0 : Nat) (r S : Nat)
    (hbd1 : 22 < bd1)
    (hbd1hi : bd1 ≤ 3 * n + 25 + 2 ^ (n / 2) + 2 + 2 * 2 ^ (n - n / 2) + 1)
    (hfit : ∀ q, f0 q < 2 ^ w) (hw1 : 1 ≤ w)
    (h1 : f0 1 = 1) (h2 : f0 2 = 0) (h7 : f0 7 = n) (h8 : f0 8 = 2 * n + 23)
    (h9 : f0 9 = n / 2) (h6 : f0 6 = bd1)
    (h11 : f0 11 = 2 ^ (n - n / 2))
    (ht0 : f0 (3 * n + 24) = t0) (ht0fit : t0 + 1 < 2 ^ w)
    (haddr : ∀ c, c ≤ BD2 n + 2 * 2 ^ (n - n / 2) + 1 → c < 2 ^ w)
    (hS : 7 * 2 ^ (n / 2) + 9 ≤ S) :
    ∃ c f', c ≤ 7 * 2 ^ (n / 2) + 9 ∧
      exec prog2 ρ S 215 r (memOf w f0)
        = exec prog2 ρ (S - c) pcScanB r (memOf w f') ∧
      arrL f' bd1 (2 ^ (n / 2)) = (arrL f0 bd1 (2 ^ (n / 2))).map (clamp t0) ∧
      f' 6 = bd1 ∧ f' 1 = 1 ∧ f' 2 = 0 ∧ f' 7 = n ∧ f' 8 = 2 * n + 23 ∧
      f' 9 = n / 2 ∧ f' 11 = 2 ^ (n - n / 2) ∧
      (∀ q, f' q < 2 ^ w) ∧ Pres (ARegC n bd1) f0 f' := by
  have h0lt : (0:Nat) < 2 ^ w := Nat.one_le_two_pow (n := w)
  have hpcc : pcCanon = 215 := rfl
  have hpcs : pcScanB = 231 := rfl
  -- the address envelope canon may touch
  have hBD : BD2 n = 3 * n + 25 + 2 * 2 ^ (n / 2) + 2 := rfl
  have haddrC : ∀ c, c ≤ bd1 + 2 ^ (n / 2) → c < 2 ^ w := by
    intro c hc
    exact haddr c (by omega)
  -- setup walk (pcs 215..221, 7 steps)
  have fit1 : ∀ q, (up f0 14 0) q < 2 ^ w := up_fit hfit (by omega)
  have fit2 : ∀ q, (up (up f0 14 0) 21 1) q < 2 ^ w := up_fit fit1 (by omega)
  have fit3 : ∀ q, (up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2))) q < 2 ^ w :=
    up_fit fit2 (haddrC (2 ^ (n / 2)) (by omega))
  have ht0l : t0 < 2 ^ w := by omega
  have fit4 : ∀ q,
      (up (up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2))) 20 (3 * n + 23)) q
        < 2 ^ w := up_fit fit3 (haddr (3 * n + 23) (by omega))
  have fit5 : ∀ q,
      (up (up (up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2))) 20 (3 * n + 23))
        20 (3 * n + 24)) q < 2 ^ w :=
    up_fit fit4 (haddr (3 * n + 24) (by omega))
  have fit6 : ∀ q,
      (up (up (up (up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2))) 20 (3 * n + 23))
        20 (3 * n + 24)) 16 t0) q < 2 ^ w :=
    up_fit fit5 ht0l
  have fit7 : ∀ q,
      (up (up (up (up (up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2)))
        20 (3 * n + 23)) 20 (3 * n + 24)) 16 t0) 22 (t0 + 1)) q < 2 ^ w :=
    up_fit fit6 ht0fit
  have hSpos : 0 < S := by omega
  have e215 : exec prog2 ρ S 215 r (memOf w f0)
      = exec prog2 ρ (S - 1) (215 + 1) r
          (memOf w (up f0 14 (f0 14 - f0 14))) :=
    exec_sub_step (S := S) hSpos
      (show prog2.getD 215 Instr.reject = Instr.sub 14 14 14 by rfl) hfit
      (by omega)
  have n215 : up f0 14 (f0 14 - f0 14) = (up f0 14 0) := by
    rw [show f0 14 - f0 14 = 0 from by omega]
  have e216 : exec prog2 ρ (S - 1) ((215 + 1)) r (memOf w (up f0 14 0))
      = exec prog2 ρ (S - 1 - 1) ((215 + 1) + 1) r
          (memOf w (up (up f0 14 0) 21 ((up f0 14 0) 1 + (up f0 14 0) 2))) :=
    exec_add_step (S := S - 1) (by omega)
      (show prog2.getD (215 + 1) Instr.reject = Instr.add 21 1 2 by rfl)
  have n216 : (up f0 14 0) 1 + (up f0 14 0) 2 = 1 := by
    rw [up_ne (show (1:Nat) ≠ 14 by omega),
        up_ne (show (2:Nat) ≠ 14 by omega), h1, h2, Nat.add_zero]
  have hmul217 : (up (up f0 14 0) 21 1) 21 * 2 ^ (up (up f0 14 0) 21 1) 9
      < 2 ^ w := by
    rw [up_eq, up_ne (show (9:Nat) ≠ 21 by omega),
        up_ne (show (9:Nat) ≠ 14 by omega), h9, Nat.one_mul]
    exact haddrC (2 ^ (n / 2)) (by omega)
  have hval217 : (up (up f0 14 0) 21 1) 21 * 2 ^ (up (up f0 14 0) 21 1) 9
      = 2 ^ (n / 2) := by
    rw [up_eq, up_ne (show (9:Nat) ≠ 21 by omega),
        up_ne (show (9:Nat) ≠ 14 by omega), h9, Nat.one_mul]
  have e217 : exec prog2 ρ (S - 1 - 1) ((215 + 1 + 1)) r (memOf w (up (up f0 14 0) 21 1))
      = exec prog2 ρ (S - 1 - 1 - 1) ((215 + 1 + 1) + 1) r
          (memOf w (up (up (up f0 14 0) 21 1) 21 ((up (up f0 14 0) 21 1) 21 * 2 ^ (up (up f0 14 0) 21 1) 9))) :=
    exec_shl_step (S := S - 1 - 1) (by omega)
      (show prog2.getD (215 + 1 + 1) Instr.reject = Instr.shl 21 21 9 by rfl) fit2
      hmul217
  have n217 : (up (up f0 14 0) 21 1) 21 * 2 ^ (up (up f0 14 0) 21 1) 9 = 2 ^ (n / 2) := hval217
  have e218 : exec prog2 ρ (S - 1 - 1 - 1) ((215 + 1 + 1 + 1)) r (memOf w (up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2))))
      = exec prog2 ρ (S - 1 - 1 - 1 - 1) ((215 + 1 + 1 + 1) + 1) r
          (memOf w (up (up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2))) 20 ((up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2))) 8 + (up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2))) 7))) :=
    exec_add_step (S := S - 1 - 1 - 1) (by omega)
      (show prog2.getD (215 + 1 + 1 + 1) Instr.reject = Instr.add 20 8 7 by rfl)
  have n218 : (up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2))) 8 + (up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2))) 7 = 3 * n + 23 := by
    rw [up_ne (show (8:Nat) ≠ 21 by omega),
        up_ne (show (8:Nat) ≠ 21 by omega),
        up_ne (show (8:Nat) ≠ 14 by omega), h8,
        up_ne (show (7:Nat) ≠ 21 by omega),
        up_ne (show (7:Nat) ≠ 21 by omega),
        up_ne (show (7:Nat) ≠ 14 by omega), h7]
    omega
  have e219 : exec prog2 ρ (S - 1 - 1 - 1 - 1) ((215 + 1 + 1 + 1 + 1)) r (memOf w (up (up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2))) 20 (3 * n + 23)))
      = exec prog2 ρ (S - 1 - 1 - 1 - 1 - 1) ((215 + 1 + 1 + 1 + 1) + 1) r
          (memOf w (up (up (up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2))) 20 (3 * n + 23)) 20 ((up (up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2))) 20 (3 * n + 23)) 20 + (up (up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2))) 20 (3 * n + 23)) 1))) :=
    exec_add_step (S := S - 1 - 1 - 1 - 1) (by omega)
      (show prog2.getD (215 + 1 + 1 + 1 + 1) Instr.reject = Instr.add 20 20 1 by rfl)
  have n219 : (up (up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2))) 20 (3 * n + 23)) 20 + (up (up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2))) 20 (3 * n + 23)) 1 = 3 * n + 24 := by
    rw [up_eq, up_ne (show (1:Nat) ≠ 20 by omega),
        up_ne (show (1:Nat) ≠ 21 by omega),
        up_ne (show (1:Nat) ≠ 21 by omega),
        up_ne (show (1:Nat) ≠ 14 by omega), h1]
  have e220 : exec prog2 ρ (S - 1 - 1 - 1 - 1 - 1) ((215 + 1 + 1 + 1 + 1 + 1)) r (memOf w (up (up (up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2))) 20 (3 * n + 23)) 20 (3 * n + 24)))
      = exec prog2 ρ (S - 1 - 1 - 1 - 1 - 1 - 1) ((215 + 1 + 1 + 1 + 1 + 1) + 1) r
          (memOf w (up (up (up (up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2))) 20 (3 * n + 23)) 20 (3 * n + 24)) 16 ((up (up (up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2))) 20 (3 * n + 23)) 20 (3 * n + 24)) ((up (up (up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2))) 20 (3 * n + 23)) 20 (3 * n + 24)) 20)))) :=
    exec_load_step (S := S - 1 - 1 - 1 - 1 - 1) (by omega)
      (show prog2.getD (215 + 1 + 1 + 1 + 1 + 1) Instr.reject = Instr.load 16 20 by rfl) fit5
  have n220 : (up (up (up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2))) 20 (3 * n + 23)) 20 (3 * n + 24)) ((up (up (up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2))) 20 (3 * n + 23)) 20 (3 * n + 24)) 20) = t0 := by
    rw [up_eq, up_ne (show (3 * n + 24) ≠ 20 by omega),
        up_ne (show (3 * n + 24) ≠ 20 by omega),
        up_ne (show (3 * n + 24) ≠ 21 by omega),
        up_ne (show (3 * n + 24) ≠ 21 by omega),
        up_ne (show (3 * n + 24) ≠ 14 by omega), ht0]
  have e221 : exec prog2 ρ (S - 1 - 1 - 1 - 1 - 1 - 1) ((215 + 1 + 1 + 1 + 1 + 1 + 1)) r (memOf w (up (up (up (up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2))) 20 (3 * n + 23)) 20 (3 * n + 24)) 16 t0))
      = exec prog2 ρ (S - 1 - 1 - 1 - 1 - 1 - 1 - 1) ((215 + 1 + 1 + 1 + 1 + 1 + 1) + 1) r
          (memOf w (up (up (up (up (up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2))) 20 (3 * n + 23)) 20 (3 * n + 24)) 16 t0) 22 ((up (up (up (up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2))) 20 (3 * n + 23)) 20 (3 * n + 24)) 16 t0) 16 + (up (up (up (up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2))) 20 (3 * n + 23)) 20 (3 * n + 24)) 16 t0) 1))) :=
    exec_add_step (S := S - 1 - 1 - 1 - 1 - 1 - 1) (by omega)
      (show prog2.getD (215 + 1 + 1 + 1 + 1 + 1 + 1) Instr.reject = Instr.add 22 16 1 by rfl)
  have n221 : (up (up (up (up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2))) 20 (3 * n + 23)) 20 (3 * n + 24)) 16 t0) 16 + (up (up (up (up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2))) 20 (3 * n + 23)) 20 (3 * n + 24)) 16 t0) 1 = t0 + 1 := by
    rw [up_eq, up_ne (show (1:Nat) ≠ 16 by omega),
        up_ne (show (1:Nat) ≠ 20 by omega),
        up_ne (show (1:Nat) ≠ 20 by omega),
        up_ne (show (1:Nat) ≠ 21 by omega),
        up_ne (show (1:Nat) ≠ 21 by omega),
        up_ne (show (1:Nat) ≠ 14 by omega), h1]
  have hmul217 : (up (up f0 14 0) 21 1) 21 * 2 ^ (up (up f0 14 0) 21 1) 9
      < 2 ^ w := by
    rw [up_eq, up_ne (show (9:Nat) ≠ 21 by omega),
        up_ne (show (9:Nat) ≠ 14 by omega), h9, Nat.one_mul]
    exact haddrC (2 ^ (n / 2)) (by omega)
  have hval217 : (up (up f0 14 0) 21 1) 21 * 2 ^ (up (up f0 14 0) 21 1) 9
      = 2 ^ (n / 2) := by
    rw [up_eq, up_ne (show (9:Nat) ≠ 21 by omega),
        up_ne (show (9:Nat) ≠ 14 by omega), h9, Nat.one_mul]
  -- setup walk (pcs 215..221, 7 steps): each step a standalone equation
  have hsetup : exec prog2 ρ S 215 r (memOf w f0)
      = exec prog2 ρ (S - 7) (215 + 7) r
          (memOf w (up (up (up (up (up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2)))
            20 (3 * n + 23)) 20 (3 * n + 24)) 16 t0) 22 (t0 + 1))) := by
    rw [e215, n215, e216, n216, e217, n217, e218, n218, e219, n219, e220,
      n220, e221, n221]
    congr 1
  have hpres7 : Pres (ARegC n bd1) f0
      (up (up (up (up (up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2)))
        20 (3 * n + 23)) 20 (3 * n + 24)) 16 t0) 22 (t0 + 1)) :=
    pres_trans (pres_up (c := 14) (show ARegC n bd1 14 from Or.inl (by omega)))
      (pres_trans (pres_up (c := 21) (show ARegC n bd1 21 from Or.inl (by omega)))
      (pres_trans (pres_up (c := 21) (show ARegC n bd1 21 from Or.inl (by omega)))
      (pres_trans (pres_up (c := 20) (show ARegC n bd1 20 from Or.inl (by omega)))
      (pres_trans (pres_up (c := 20) (show ARegC n bd1 20 from Or.inl (by omega)))
      (pres_trans (pres_up (c := 16) (show ARegC n bd1 16 from Or.inl (by omega)))
      (pres_up (c := 22) (show ARegC n bd1 22 from Or.inl (by omega))))))))
  -- the loop
  obtain ⟨cL, f', hcL, hexL, h14', h21', h16', h22', h6', h1', h2', h7', h8',
    h9', h11', hfit', hB', hpres'⟩ :=
    canonLoop_exec ρ f0 bd1 t0 (2 ^ (n / 2)) 0
      (up (up (up (up (up (up (up f0 14 0) 21 1) 21 (2 ^ (n / 2)))
        20 (3 * n + 23)) 20 (3 * n + 24)) 16 t0) 22 (t0 + 1)) (S - 7) r
      hbd1
      (by rw [up_ne (show (1:Nat) ≠ 22 by omega),
              up_ne (show (1:Nat) ≠ 16 by omega),
              up_ne (show (1:Nat) ≠ 20 by omega),
              up_ne (show (1:Nat) ≠ 20 by omega),
              up_ne (show (1:Nat) ≠ 21 by omega),
              up_ne (show (1:Nat) ≠ 21 by omega),
              up_ne (show (1:Nat) ≠ 14 by omega), h1])
      (by rw [up_ne (show (2:Nat) ≠ 22 by omega),
              up_ne (show (2:Nat) ≠ 16 by omega),
              up_ne (show (2:Nat) ≠ 20 by omega),
              up_ne (show (2:Nat) ≠ 20 by omega),
              up_ne (show (2:Nat) ≠ 21 by omega),
              up_ne (show (2:Nat) ≠ 21 by omega),
              up_ne (show (2:Nat) ≠ 14 by omega), h2])
      (by rw [up_ne (show (7:Nat) ≠ 22 by omega),
              up_ne (show (7:Nat) ≠ 16 by omega),
              up_ne (show (7:Nat) ≠ 20 by omega),
              up_ne (show (7:Nat) ≠ 20 by omega),
              up_ne (show (7:Nat) ≠ 21 by omega),
              up_ne (show (7:Nat) ≠ 21 by omega),
              up_ne (show (7:Nat) ≠ 14 by omega), h7])
      (by rw [up_ne (show (8:Nat) ≠ 22 by omega),
              up_ne (show (8:Nat) ≠ 16 by omega),
              up_ne (show (8:Nat) ≠ 20 by omega),
              up_ne (show (8:Nat) ≠ 20 by omega),
              up_ne (show (8:Nat) ≠ 21 by omega),
              up_ne (show (8:Nat) ≠ 21 by omega),
              up_ne (show (8:Nat) ≠ 14 by omega), h8])
      (by rw [up_ne (show (9:Nat) ≠ 22 by omega),
              up_ne (show (9:Nat) ≠ 16 by omega),
              up_ne (show (9:Nat) ≠ 20 by omega),
              up_ne (show (9:Nat) ≠ 20 by omega),
              up_ne (show (9:Nat) ≠ 21 by omega),
              up_ne (show (9:Nat) ≠ 21 by omega),
              up_ne (show (9:Nat) ≠ 14 by omega), h9])
      (by rw [up_ne (show (6:Nat) ≠ 22 by omega),
              up_ne (show (6:Nat) ≠ 16 by omega),
              up_ne (show (6:Nat) ≠ 20 by omega),
              up_ne (show (6:Nat) ≠ 20 by omega),
              up_ne (show (6:Nat) ≠ 21 by omega),
              up_ne (show (6:Nat) ≠ 21 by omega),
              up_ne (show (6:Nat) ≠ 14 by omega), h6])
      (by rw [up_ne (show (11:Nat) ≠ 22 by omega),
              up_ne (show (11:Nat) ≠ 16 by omega),
              up_ne (show (11:Nat) ≠ 20 by omega),
              up_ne (show (11:Nat) ≠ 20 by omega),
              up_ne (show (11:Nat) ≠ 21 by omega),
              up_ne (show (11:Nat) ≠ 21 by omega),
              up_ne (show (11:Nat) ≠ 14 by omega), h11])
      (by rw [up_ne (show (21:Nat) ≠ 22 by omega),
              up_ne (show (21:Nat) ≠ 16 by omega),
              up_ne (show (21:Nat) ≠ 20 by omega),
              up_ne (show (21:Nat) ≠ 20 by omega),
              up_eq])
      (by rw [up_ne (show (16:Nat) ≠ 22 by omega), up_eq])
      (by rw [up_eq])
      (by rw [up_ne (show (14:Nat) ≠ 22 by omega),
              up_ne (show (14:Nat) ≠ 16 by omega),
              up_ne (show (14:Nat) ≠ 20 by omega),
              up_ne (show (14:Nat) ≠ 20 by omega),
              up_ne (show (14:Nat) ≠ 21 by omega),
              up_ne (show (14:Nat) ≠ 21 by omega), up_eq])
      (by omega) hfit fit7 haddrC (fun q hq => absurd hq (by omega))
      (by intro q _ hq2
          rw [up_ne (show (bd1:Nat) + q ≠ 22 by omega),
              up_ne (show (bd1:Nat) + q ≠ 16 by omega),
              up_ne (show (bd1:Nat) + q ≠ 20 by omega),
              up_ne (show (bd1:Nat) + q ≠ 20 by omega),
              up_ne (show (bd1:Nat) + q ≠ 21 by omega),
              up_ne (show (bd1:Nat) + q ≠ 21 by omega),
              up_ne (show (bd1:Nat) + q ≠ 14 by omega)])
      hpres7 (by omega) (by omega)
  refine ⟨7 + cL, f', by omega, ?_, ?_, h6', h1', h2', h7', h8', h9', h11',
    hfit', hpres'⟩
  · rw [hsetup, show (215 + 7) = 222 from rfl, hexL,
      show S - 7 - cL = S - (7 + cL) from by omega, hpcs]
  · rw [arrL_congr (g := fun c => clamp t0 (f0 c))
      (fun q _ => hB' q (by omega))]
    simp [arrL, arrAt, List.map_map, Function.comp]

end SubsetSum.MITM
