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

end SubsetSum.MITM
