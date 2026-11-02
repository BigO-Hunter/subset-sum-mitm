import Submission.Det
set_option autoImplicit true

/-!
# Concrete facts about `prog` (R2125607414)

`prog` is a closed list; no-`rand` is checkable by evaluation.
-/

namespace SubsetSum.MITM

open BigOSpeedrun.SubsetSum

/-- Bool classifier: is this instruction a `rand`? -/
def isRandInstr : Instr → Bool
  | .rand _ => true
  | _ => false

set_option maxRecDepth 10000 in
/-- The emitted program contains no `rand` instruction. -/
theorem prog_no_rand : NoRand prog := by
  intro p hp i he
  have hall : prog.all (fun q => !isRandInstr q) = true := by decide
  have h1 : (!isRandInstr p) = true := List.all_eq_true.mp hall p hp
  rw [he] at h1
  simp [isRandInstr] at h1

set_option maxRecDepth 10000 in
/-- v2 S3 GATE: the same decide closes on the longer v2 program shape.
prog2 = 310 instructions vs prog = 249 (probed 2026-11-01); the risk-2
question was whether the ~25% longer list still decides under
`maxRecDepth 10000`.  Verdict: it does — no raise needed, the
determinism route survives the v2 program shape. -/
theorem prog2_no_rand : NoRand prog2 := by
  intro p hp i he
  have hall : prog2.all (fun q => !isRandInstr q) = true := by decide
  have h1 : (!isRandInstr p) = true := List.all_eq_true.mp hall p hp
  rw [he] at h1
  simp [isRandInstr] at h1

end SubsetSum.MITM
