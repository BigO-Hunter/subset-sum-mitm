import Submission.PhaseA
import Submission.Sort

namespace Probe

-- probe core lemma availability
#check @List.Pairwise.map
#check @List.mem_map
example (s : Nat) : s + 1 ≤ 2 ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Nat.pow_succ]
    have h : (2:Nat) * (s + 1) = s + 1 + (s + 1) := by omega
    omega

end Probe
