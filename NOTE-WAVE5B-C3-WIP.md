# Wave 5b — §C3 WIP: bign_run2_from148 (~90% drafted, 6 localized errors left)

WIP file: /private/tmp/opencode/RaceV2.wip-c3.lean (copy over
Submission/RaceV2.lean to resume). The committed branch state (791985a)
is GREEN; the WIP adds only `bign_run2_from148` (~150 lines at file end,
after §C2 helpers). All ingredients are committed and green.

## What the WIP theorem looks like

`bign_run2_from148` (statement complete and correct, inserted before the
#print axioms scanLoop_accepts line): phaseA-exit contract (hypotheses
f0/bd1/t0/h18/h6/hb1/harr/ht0/ht0v/haddr/hrel/hin + hS : 176·2^(n/2)+64n ≤ S)
⇒ exec prog2 ρ S 148 r (memOf w f0) = some (decide (isSum (instA x) n x.t)).
Needs `open scoped Classical in` BEFORE its docstring (currently after —
parse error), for the decide-shaped summit statement (Race.lean idiom).

## The 6 remaining errors (all localized, all mechanical)

1. `open scoped Classical in` placement: move it BEFORE the /-- docstring
   of bign_run2_from148 (currently between docstring and theorem → parse
   error at the `open`).
2. hpresAB: my ∃-free value-at-position attempt used getElem notation
   whose index side-goal get_elem_tactic can't close (arrL is a def, not
   simp-unfoldable). FIX: deleted `arrL_getElem`; the committed §C2 has
   `arrL_mem`/`arrL_mem_pos`. Add (BEFORE §C2 helpers, with @[simp]):
   ```lean
   @[simp] theorem arrL_length {f : Nat → Nat} {b L : Nat} :
       (arrL f b L).length = L := by unfold arrL; simp
   theorem arrL_val {f : Nat → Nat} {b L q : Nat} (hq : q < L) :
       (arrL f b L)[q]? = some (f (b + q)) := by
     unfold arrL arrAt
     rw [List.getElem?_map, List.getElem?_range]
     all_goals simp [hq]
   ```
   (the `all_goals` mops up both the if-goal and the q<L side-goal).
   Then hpresAB := intro q hq; have h1 := arrL_val hq;
   rw [hf''arr, List.getElem?_map, arrL_val hq] at h1; simpa using h1.symm.
   (The WIP file's hpresAB block shows the intended shape — swap its
   getElem-based body for the ?-form.)
3. setup7 bullet alignment: the pin bullets are now g1,g2,g6,g12,g7,g11,
   g13,g17,g19,g22,gT,g8,g9,cellpres,fit,c but the refine order (and the
   statement ∧-order) is g1,g2,g6,g12,g13,g17,g19,g22,gT,g7,g8,g9,g11,
   cellpres,fit,addr — i.e. MOVE the g7+g11 bullets to sit between gT and
   g8 (they currently sit between g12 and g13). refine arity: 16 ?_'s.
4. setup7 needs two MORE exports for scanB_exec's h7/h11: `g 7 = f 7` and
   `g 11 = f 11` (peels: (7≠22)×2,(7≠17),(7≠20)×2,(7≠13),(7≠12),h7 and
   the 11-analogue). Statement: insert `g 7 = n ∧ g 11 = 2^(n-n/2) ∧`
   after `g (3*n+24) = t0 ∧`; refine: two more ?_'s; bullets: two more
   up_ne-peel bullets. (The composer's scanB_exec call then passes
   `hg7`/`hg11` where the WIP wrote `rw [hg7]`/`rw [hg11]` on nonexistent
   names — the obtain destructure list also needs hg7/hg11 inserted.)
5. Fuel omegas: the haves hpownnz/hpownnz2/hpow2/hbc must sit BEFORE the
   canon/setup7/scanB/scanLoop applications (WIP has hbc+hnns mid-proof —
   MOVE to the top, right after hw1). hpow2's proof:
   ```lean
   have hpow2 : 2 ^ (n - n / 2) ≤ 2 * 2 ^ (n / 2) := by
     have h1 : 2 ^ (n - n / 2) ≤ 2 ^ (n / 2 + 1) :=
       Nat.pow_le_pow_right (by omega) (by omega)
     rw [Nat.pow_succ] at h1
     omega
   ```
   plus hBnn1/hBnn2 (already in WIP) — then ALL fuel (by omega)s close:
   canon 7·2^(n/2)+9 ≤ S-c₂, setup7 7 ≤ S-c₂-c₃, scanB/loop
   10·(2^(n/2)+2^(n-n/2))+9 ≤ S-c₂-c₃ (scanB_exec's budget via
   budget_compose2's fold: 30·2^(n/2)+9 ≥ 10·(2^(n/2)+2^(n-n/2))+9 needs
   hpow2 only).
6. setup7's ht0-arg: the WIP passes `(by rw [...rfl...]; exact hpresT)` —
   wrong state (hpresT is f' not f''). Add `hpresT'' : f'' (3n+24) = t0`
   via hf''pres (3n+24 ∉ ARegC: rcases <;> omega) then hpresT, and pass
   THAT. Also delete the WIP's leftover `hpow2` duplicate at old position
   (the one after -- scanB envelope facts) and the silly
   `rw [show S - c₂ - c₃ - c₄ = ... from rfl] at *` line (identity rw at *
   can loop); the completeness hex-chain's second rw (S-show) is unneeded.

## Composer call notes (verified against the committed signatures)

- phaseA2_exec ρ hn hw f0 r S hfit h1 h2 h7 h8 h9 h10 h18 hb1 harr haddr
  hrel hin (by omega) — h18 : f0 18 = bd1 EXPLICIT bd1.
- canon_exec ρ f' bd1 t0 r (S-c₂) (22<bd1 via hb1+omega) (bd1hi via hb1)
  hf'fit hw1 hf'1 hf'2 hf'7 hf'8 hf'9 hf'6 hf'11 ht0' ht0fit haddr (by omega)
  where ht0' : f'(3n+24) = t0 via hf'pres (∉AReg2) + ht0;
  ht0fit : t0+1 < 2^w via x.t ≤ maxValue < 2^bits < 2^w (bits < w since
  wordLength = 4(n+bits)+log2+1, unfold at hw; use a hw' COPY — unfolding
  at hw mutates it for later hw1-use).
- scanB_exec h-pins from setup7 exports: h1:=hg1 h2:=hg2 h6:=hg6 h7:=hg7
  h8:=hg8 h9:=hg9 h11:=hg11 h19:=hg19 ht0:=hgT(3n+24) — hgT IS the t-pin.
- scanLoop_accepts hpair-λ: goal is g-cells — rw [hgcellpres q (by omega),
  hgcellpres q' (by omega)] then hpair'' q hq q' hq'.
- The witness-goal (hfind) needs the same cellpres rws around
  hcell₁/hcell₂, and canon_pair_iff closes with ht0v-rw on the GOAL
  (t0 → x.t) BEFORE .mpr (see WIP lines ~1195).
- Final assembly: rw [hex, ht0v]; congr 1;
  exact (decide_eq_true_iff.mpr his).symm.
- scanLoop_accepts' fuel: 10·(2^(n/2)+2^(n-n/2))+2 ≤ S-c₂-c₃-7 ✓ omega.
- Axioms: bign_run2_from148 will carry Classical.choice (decide-shaped
  summit, `open scoped Classical in` — Race.lean's Race_bound does the
  same). Everything else stays [propext, Quot.sound].
