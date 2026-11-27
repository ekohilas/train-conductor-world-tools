/-
Not part of the library. Prints the output of the verified reduction `toK` on two small
instances, so that it can be compared with the Python generator
`network_solver.sat.to_sat` (see tests/test_sat_reduction.py, `test_matches_lean_reduction`).

  cd lean && lake env lean Check/CompareWithPython.lean
-/
import TrainNetwork.GoalForward

open TrainNetwork

def inst2 : Instance where
  W := 3
  H := 2
  blocked := {(1, 0)}
  ports := {(0, 0), (2, 1)}
  cities := {(2, 0), (0, 1)}
  k := 1
  k_pos := by decide
  k_le_cities := by decide
  ports_cities := by decide
  ports_unblocked := by decide
  cities_unblocked := by decide
  ports_inBounds := by decide
  cities_inBounds := by decide
  blocked_inBounds := by decide

#eval IO.println (toString (Answer.toK tinyInstance 0 1).val.clauses)
#eval IO.println (toString (Answer.toK inst2 1 2).val.clauses)
#eval IO.println (toString ((Answer.toK inst2 1 2).time, (Answer.toK inst2 1 2).val.size))
