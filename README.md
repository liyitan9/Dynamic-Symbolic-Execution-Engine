# ECE 653 Spring 2025 Project

This project includes multiple execution engines and related test infrastructure:

- `concolic_incremental.py`: EXE-style concolic execution engine with incremental solving using Z3's scopes interface.
- `concolic.py`: Basic concolic execution engine without solver state reuse.
- `sym_only.py`: Symbolic execution engine as implemented in Assignment 2.

## Testing

- Comprehensive test cases for full statement and branch coverage of `concolic_incremental.py` are provided in `test_project.py`.
- Tests can be run using the following command:
  ```bash
  python3 -m wlang.test
- A coverage report can be generated using: coverage run --branch -m wlang.test
- `test_sym.py` contains two divergent test cases used for runtime performance analysis for symbolic execution engine only.