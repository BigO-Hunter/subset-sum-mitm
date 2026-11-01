import Submission.Race

/-- The submission target: subset-sum in O(2^(0.75n)). -/
theorem Race.bound : BigOSpeedrun.SubsetSum.SolvedInTime (3 / 4 : Rat) :=
  SubsetSum.MITM.Race_bound_reduced
