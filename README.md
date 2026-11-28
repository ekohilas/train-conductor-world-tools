# Train Conductor World Tools

This repository is a collection of tools to help with the creation and validation of manually made track networks for
the Train Conductor World Map.

The tool works by running alongside an open instance of `train-conductor-world.tmx` within [Tiled Map Editor][1]

The required data for the tool, such as the distances, tiles list, and tiled map can be
found [here](https://github.com/ekohilas/train-conductor-world-map).

1. Ensure the required version of Python in `.python-version` is installed.
    * One way this can be done is by running `pyenv install` after [pyenv](https://github.com/pyenv/pyenv#installation)
      is installed.
1. Ensure the requirements are installed.
    * With [Poetry](https://python-poetry.org/docs/#installation), this is achieved through
      running `poetry env use python && poetry install`
    * Alternatively, one can run `python -m pip install .`
1. [Tiled Map Editor][1] can be downloaded [here](https://www.mapeditor.org/download.html).

## Usage

1. Open `train-conductor-world.tmx` in Tiled Map Editor.
1. Run `main.py` e.g.:
    * `poetry run python train_conductor_world_helper/main.py`
    * `python3 train_conductor_world_helper/main.py`
1. Inside Tiled Map Editor, make an edit to the track network and save.
1. Watch as:
    * Within the Tiled Map Editor, the connections between the ports and cities are updated through the annotations
      layer.
    * From the Python output, validations are logged informing you of issues.
1. Repeat.

## Example

![](./annotations.png)

## Network optimisation and complexity research

The problem of laying out the cheapest track network is defined formally in
[`docs/problem.md`](docs/problem.md). The definition is frozen and shared by the solver,
the verifier and the Lean formalisation.

* `python -m network_solver extract`: rebuild `data/instances/europe.json` from the Tiled map.
* `python -m network_solver solve data/instances/europe.json --out solution.json`:
  exact CP-SAT solver. It minimises total excess path length first, then track tiles.
* `python -m network_solver verify data/instances/europe.json solution.json`: an
  independent checker.
* `python -m pytest -q`: tests, including brute-force cross-checks of the solver.
* `lean/`: Lean 4 + Mathlib formalisation (`cd lean && lake exe cache get && lake build`).

### Complexity with few terminals: status

[`docs/result.md`](docs/result.md) reports on the question "is there a quasi-polynomial
exact algorithm for at most 10 ports and 40 cities?". **The answer was not found.** What
exists:

* `lean/TrainNetwork/Answer.lean`: a machine-checked exact solver (exhaustive search)
  with a proved *exponential* time bound. `cd lean && lake build TrainNetwork.Partial`
  builds everything that is proved. `lake build` fails at `Goal.lean`, on purpose,
  because the quasi-polynomial bound `Answer.quasipoly` is not proved.
* `python -m network_solver.exhaustive INSTANCE`: the same exhaustive search in Python
  (tiny instances only).
* `python -m network_solver.frontier INSTANCE`: an exact frontier dynamic program,
  subexponential for a bounded number of terminals (small instances only).
* `tests/test_exact_algorithms.py`: both are compared with the CP-SAT oracle.

## TODO

* Add tests
* Add annotations for shortest bounds
* Improve annotation code, possibly with decorators or context managers.
* Fix pylint import errors in pycharm
* Finalize type annotations

[1]: https://www.mapeditor.org/