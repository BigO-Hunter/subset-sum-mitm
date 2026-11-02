import Submission.PhaseA
import Submission.Sort
set_option autoImplicit true

/-!
# Phase A2: entry plumbing for the v2 second-half merge (v2 M2)

Compile-level plumbing only — the full `phaseA2_exec` is task PH2.
This file pins what PH2's caller will consume:

§1 `AReg2 n` — phaseA2's write region: the register file (cells ≤ 22)
   plus the two second-half strips above both first-half arrays
   (`bd2 = 3n+25+2^(n/2+1)+2`, two strips of `2^(n−n/2)` plus the
   one-cell separator).  Conservative superset of the writes the
   `phaseA2` program in `Program.lean` actually performs, so `Pres
   (AReg2 n)` is provable for it in PH2 and composable downstream.

§2 `hrel2_of_pres` — the second-half source-address facts.  The
   relocated input block (`RELOC+1 .. RELOC+n+1` = `2n+24 .. 3n+24`)
   lies outside `AReg n`, so phaseA's `Pres (AReg n)` carries every
   `hrel` cell across phaseA unchanged; shifting the index by `n/2`
   turns them into exactly PH2's `hrel2` hypothesis.  This is the
   Race.lean 588–594 pattern, factored out once for the v2 caller.

§3 `block_not_AReg2` — the same block (and the `t` cell `3n+24`) also
   lies outside `AReg2 n`, so later v2 stages (canon, scanB) keep the
   block through a `Pres (AReg2 n)` post-state the same way.
-/

namespace SubsetSum.MITM

open BigOSpeedrun.SubsetSum SubsetSum.MITM.Spec

/-! ## §1. The phaseA2 write region -/

/-- phaseA2's write region: registers (cells ≤ 22) plus the second-half
strips above the first-half arrays. -/
def AReg2 (n : Nat) (c : Nat) : Prop :=
  c ≤ 22 ∨ (3 * n + 25 + 2 ^ (n / 2 + 1) + 2 ≤ c ∧
    c < 3 * n + 25 + 2 ^ (n / 2 + 1) + 2 + 2 ^ (n - n / 2 + 1))

/-! ## §2. The second-half source-address facts (PH2's `hrel2`) -/

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

/-! ## §3. The block survives later v2 stages too -/

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

end SubsetSum.MITM
