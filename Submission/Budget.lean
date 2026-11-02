set_option autoImplicit true

/-!
# Budget: squaring `T n = C*2^(n/2) + D*n` into `2 ^ n` (v2, α = 1/2)

The board contract at α = 1/2 needs `T n ^ 2 ≤ K * 2 ^ n` for every `n ≥ 2`,
one `K`. With `T n = C * 2 ^ (n / 2) + D * n` the constant is
`K = C*C + 2*C*D + 2*D*D` (report §3(B)); `C`, `D` stay abstract here —
the discharge wave plugs the phase constants.

House rule: `omega` treats `2 ^ _` as an atom, so every exponent fact is
carried as an explicit lemma and powers are folded only by monotonicity
(`Nat.pow_le_pow_right`), never by handing `omega` a goal with two distinct
powers in it.
-/

namespace SubsetSum.MITM

/-- `2 ^ (2 * (n / 2)) ≤ 2 ^ n` — the atom-fold. `omega` cannot relate the
two powers on its own; the exponent fact `2 * (n / 2) ≤ n` is a plain Nat
division fact (`Nat.mul_div_le`), and the fold is monotonicity. No parity
case split is needed. -/
theorem pow_fold (n : Nat) : 2 ^ (2 * (n / 2)) ≤ 2 ^ n :=
  Nat.pow_le_pow_right (by omega) (Nat.mul_div_le n 2)

/-- `j + 1 ≤ 2 ^ j` — the small engine behind the ceiling facts below. -/
private theorem succ_le_pow (j : Nat) : j + 1 ≤ 2 ^ j := by
  induction j with
  | zero => rw [Nat.pow_zero]; omega
  | succ j ih => rw [Nat.pow_succ]; omega

/-- `n ≤ 2 ^ (n - n / 2)`, i.e. `n ≤ 2 ^ ceil(n / 2)` in Nat semantics.
True for every `n`; the report's bases read `n = 2: 2 ≤ 2`, `n = 3: 3 ≤ 4`,
`n = 4: 4 ≤ 4`, and the exponential dominates from there. -/
theorem n_le_two_pow_ceil (n : Nat) : n ≤ 2 ^ (n - n / 2) := by
  have main : ∀ k : Nat, 2 * k ≤ 2 ^ k ∧ 2 * k + 1 ≤ 2 ^ (k + 1) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact ⟨by omega, by decide⟩
    · have hkm : k ≤ 2 ^ (k - 1) := by
        have h := succ_le_pow (k - 1)
        omega
      have e : k - 1 + 1 = k := by omega
      have hp1 : 2 ^ k = 2 ^ (k - 1) * 2 := by
        rw [show 2 ^ k = 2 ^ (k - 1 + 1) from by rw [e], Nat.pow_succ]
      have hp2 : 2 ^ (k + 1) = 2 ^ k * 2 := by rw [Nat.pow_succ]
      have hk1 : k + 1 ≤ 2 ^ k := succ_le_pow k
      exact ⟨by rw [hp1]; omega, by rw [hp2]; omega⟩
  rcases Nat.mod_two_eq_zero_or_one n with hm | hm
  · have hnk : n = 2 * (n / 2) := by omega
    have hke : n - n / 2 = n / 2 := by omega
    calc n = 2 * (n / 2) := hnk
      _ ≤ 2 ^ (n / 2) := (main (n / 2)).1
      _ = 2 ^ (n - n / 2) := by rw [hke]
  · have hnk : n = 2 * (n / 2) + 1 := by omega
    have hke : n - n / 2 = n / 2 + 1 := by omega
    calc n = 2 * (n / 2) + 1 := hnk
      _ ≤ 2 ^ (n / 2 + 1) := (main (n / 2)).2
      _ = 2 ^ (n - n / 2) := by rw [hke]

/-- `n * 2 ^ (n / 2) ≤ 2 ^ n` — the middle-term fold: `n ≤ 2 ^ (n - n/2)`
recombines with `2 ^ (n / 2)` by `Nat.pow_add` (the exponents sum to `n`). -/
theorem n_mul_half_le (n : Nat) : n * 2 ^ (n / 2) ≤ 2 ^ n := by
  have h1 : n ≤ 2 ^ (n - n / 2) := n_le_two_pow_ceil n
  have h2 : 2 ^ n = 2 ^ ((n - n / 2) + n / 2) := by
    have e : (n - n / 2) + n / 2 = n := by omega
    rw [e]
  rw [h2, Nat.pow_add]
  exact Nat.mul_le_mul h1 (Nat.le_refl _)

/-- `n * n ≤ 2 * 2 ^ n` — true for every `n` (max of `n² / 2ⁿ` is `9 / 8`
at `n = 3`). Induction step: `(n+1)² = n² + 2n + 1` and `2n + 1 ≤ 2^(n+1)`. -/
theorem n_sq_le (n : Nat) : n * n ≤ 2 * 2 ^ n := by
  induction n with
  | zero => rw [Nat.pow_zero]; omega
  | succ n ih =>
    have h1 : (n + 1) * (n + 1) = n * n + n + n + 1 := by
      show Nat.succ n * Nat.succ n = _
      rw [Nat.mul_succ, Nat.succ_mul]
      omega
    have hp : 2 * 2 ^ (n + 1) = 2 * 2 ^ n * 2 := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    rw [h1, hp]
    have hs := succ_le_pow n
    omega

/-- The budget theorem (report §3(B)): for `T n = C * 2 ^ (n / 2) + D * n`,
`(T n) ^ 2 ≤ (C * C + 2 * C * D + 2 * D * D) * 2 ^ n`. Expand the square,
fold term 1 by `pow_fold`, term 2 by `n_mul_half_le`, term 3 by `n_sq_le`,
and collect into `K = C² + 2CD + 2D²` times `2 ^ n`. `C`, `D` are abstract;
true for every `n` (hence a fortiori for `n ≥ 2`). -/
theorem budget_sq (C D n : Nat) (hn : 2 ≤ n) :
    (C * 2 ^ (n / 2) + D * n) ^ 2 ≤ (C * C + 2 * C * D + 2 * D * D) * 2 ^ n := by
  have hpf := pow_fold n
  have hnm := n_mul_half_le n
  have hns := n_sq_le n
  -- canonical atom shapes for the four products of the expansion
  have hXX : C * 2 ^ (n / 2) * (C * 2 ^ (n / 2)) = C * C * 2 ^ (2 * (n / 2)) := by
    rw [Nat.mul_mul_mul_comm, ← Nat.pow_add,
      show (n / 2) + (n / 2) = 2 * (n / 2) from by omega]
  have hXY : C * 2 ^ (n / 2) * (D * n) = C * D * (n * 2 ^ (n / 2)) := by
    rw [Nat.mul_mul_mul_comm, Nat.mul_comm (2 ^ (n / 2)) n]
  have hYX : D * n * (C * 2 ^ (n / 2)) = C * D * (n * 2 ^ (n / 2)) := by
    rw [Nat.mul_comm (D * n) (C * 2 ^ (n / 2)), hXY]
  have hYY : D * n * (D * n) = D * D * (n * n) := by
    rw [Nat.mul_mul_mul_comm]
  -- expand the square, land each product on its canonical atom
  rw [Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_add, hXX, hXY, hYX, hYY]
  -- block bounds: each by monotone scaling of one support fact
  have b1 : C * C * 2 ^ (2 * (n / 2)) ≤ C * C * 2 ^ n := Nat.mul_le_mul (Nat.le_refl _) hpf
  have b2 : C * D * (n * 2 ^ (n / 2)) ≤ C * D * 2 ^ n := Nat.mul_le_mul (Nat.le_refl _) hnm
  have b3 : D * D * (n * n) ≤ D * D * (2 * 2 ^ n) := Nat.mul_le_mul (Nat.le_refl _) hns
  refine Nat.le_trans (Nat.add_le_add (Nat.add_le_add b1 b2) (Nat.add_le_add b2 b3)) ?_
  -- distribute the RHS over K's summands; the remaining bookkeeping is linear
  -- in the product atoms, which omega closes
  rw [Nat.two_mul (2 ^ n), Nat.mul_add (D * D) (2 ^ n) (2 ^ n)]
  rw [Nat.mul_assoc 2 C D, Nat.mul_assoc 2 D D]
  rw [Nat.add_mul (C * C + 2 * (C * D)) (2 * (D * D)) (2 ^ n)]
  rw [Nat.add_mul (C * C) (2 * (C * D)) (2 ^ n)]
  rw [Nat.mul_assoc 2 (C * D) (2 ^ n), Nat.mul_assoc 2 (D * D) (2 ^ n)]
  generalize hp1 : C * C * 2 ^ n = p1
  generalize hp2 : C * D * 2 ^ n = p2
  generalize hp3 : D * D * 2 ^ n = p3
  omega

/-- Explicit small-base checks (S5 acceptance: `n = 2, 3` pinned by `decide`). -/
example : (2 : Nat) ≤ 2 ^ (2 - 2 / 2) := by decide
example : (3 : Nat) ≤ 2 ^ (3 - 3 / 2) := by decide
example : (4 : Nat) ≤ 2 ^ (4 - 4 / 2) := by decide
example : (2 : Nat) * 2 ^ (2 / 2) ≤ 2 ^ 2 := by decide
example : (3 : Nat) * 2 ^ (3 / 2) ≤ 2 ^ 3 := by decide
example : (2 : Nat) * 2 ≤ 2 * 2 ^ 2 := by decide
example : (3 : Nat) * 3 ≤ 2 * 2 ^ 3 := by decide

#print axioms pow_fold
#print axioms succ_le_pow
#print axioms n_le_two_pow_ceil
#print axioms n_mul_half_le
#print axioms n_sq_le
#print axioms budget_sq

end SubsetSum.MITM
