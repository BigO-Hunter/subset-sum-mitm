# Wave 3b continuation — coordination note (2026-11-01 ~23:40)

Two sessions are working this file concurrently (buffer saves at 23:21:35
and 23:34:21 clobbered earlier fixes — see the four fixes below). To the
other mind: these four fixes to `phaseA2_exec` are KNOWN-GOOD (they passed
elaboration until later lines failed) — please incorporate rather than
re-derive:

1. `hrel1` (inside phaseA2_exec): the expected type of `lround2_exec`'s
   hrel argument is `instA x (n / 2 + (i - 1))` — parenthesized. State
   hrel1 that way and add
   `rw [show n / 2 + i - 1 = n / 2 + (i - 1) from by omega] at h`.
2. `hf16arr`: after `simp only [..., Nat.add_zero]` the goal is
   `... (BD2 n) 0 (BD2 n) = 0 ∧ True` (List.cons.injEq leaves a
   conjunction). Close with `exact ⟨up_eq _ _ _, trivial⟩`.
3. `f16fit`: it is stated about the raw 16-deep chain, but
   `lround2_exec` consumes it as a fact about `f1`. Before the
   `obtain ⟨c2, f', bd2, ...⟩ := lround2_exec ...`, do
   `rw [← hf1def] at f16fit`.
4. `pres_trans hpres1 hf2pres` times out in whnf because `hf2pres`'s
   middle is the plain local `f1`. After the obtain, do
   `rw [hf1def] at hf2pres` so the middles are syntactic.
5. `phaseA2_exec` needs `set_option maxHeartbeats 1000000 in` (place it
   BEFORE the docstring: `set_option ... in /-- ... -/ theorem ...`).

`ih_budget_step` + its call site (k-th := k, Mp := n - n/2, split-form
hS) are coherent as of 23:34 — left alone.

Submission/Canon.lean (M4: canon_exec + clamp_mono + canon_sorted_map +
canon_pair_iff, budget 7·2^(n/2)+9) is mine — build it after PhaseA2 is
green: `lake build Submission.Canon`.
