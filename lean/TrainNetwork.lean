import TrainNetwork.Problem
import TrainNetwork.Cost
import TrainNetwork.Walks
import TrainNetwork.Exec
import TrainNetwork.Search
import TrainNetwork.Timed
import TrainNetwork.TimeBound
import TrainNetwork.Answer
import TrainNetwork.Partial
-- `Goal.lean` does NOT build: `Answer.quasipoly` is not proved (see docs/result.md).
-- Everything above builds: `lake build TrainNetwork.Partial`.
import TrainNetwork.Goal
