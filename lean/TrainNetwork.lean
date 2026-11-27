import TrainNetwork.Problem
import TrainNetwork.Cost
-- `TrainNetwork.Goal` is NOT imported: its backward half (`fromK`, `from_correct`,
-- `from_poly`) is not proved, so it does not compile. The forward half is proved and
-- restated verbatim in `TrainNetwork.GoalForward`. See docs/result.md, "Status".
import TrainNetwork.GoalForward
