import TrainNetwork.Problem
import TrainNetwork.Cost
import TrainNetwork.Partial
-- `TrainNetwork.Goal` is deliberately NOT imported: the goal was not reached.
-- `TrainNetwork/Answer.lean` does not exist, because we have no polynomial-time
-- algorithm and hence no `Answer.polytime`. `lake build TrainNetwork.Goal` fails.
-- What is proved instead is in `TrainNetwork/Partial.lean`; see docs/result.md.
