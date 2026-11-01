import Submission.Race

/-- The submission target: subset-sum in O(2^(0.75n)). -/
theorem Race.bound : BigOSpeedrun.SubsetSum.SolvedInTime (75 / 100 : Rat) :=
  SubsetSum.MITM.Race_bound
