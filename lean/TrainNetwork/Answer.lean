/-
The answer, as far as it is proved.

Known problem: SATISFIABILITY of CNF formulas (`KInstance`, `KInstance.size`, `KYes` in
`TrainNetwork/Sat.lean`).

Proved here (forward half of `Goal.lean`):
* `toK`        : the reduction Train Network → SAT, written in `TimeM` (`Gen.lean`);
* `to_correct` : `Decide I X K ↔ KYes (toK I X K).val` (`Forward.lean`);
* `to_poly`    : `toK` runs in polynomial time with polynomially bounded output.

NOT proved: the backward half (`fromK`, `from_correct`, `from_poly`). `Goal.lean`
therefore does not compile against this file, and it is deliberately not imported from
`TrainNetwork.lean`. See docs/result.md, section "Status".
-/
import TrainNetwork.Forward
