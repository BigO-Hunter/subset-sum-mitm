import Submission.Prog2BigO

/-- The submission target: subset-sum in O(2^(1/2n)). -/
theorem Race.bound : BigOSpeedrun.SubsetSum.SolvedInTime (1 / 2 : Rat) :=
  SubsetSum.MITM.Race_bound'
