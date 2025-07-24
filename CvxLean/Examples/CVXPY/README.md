# CVXPY to CVXLean Integration Tools

Complete toolkit for converting CVXPY optimization problems to CVXLean Lean code, enabling the use of Python-defined optimization problems within the Lean theorem prover's formal verification framework.

## Overview

This toolkit provides a complete pipeline from CVXPY (Python convex optimization) to CVXLean (Lean theorem prover optimization framework):

```
CVXPY Problem → JSON (S-expressions) → Lean Code → CVXLean Integration
```

## Installation

1. **Prerequisites:**
   - Python 3.7+ with CVXPY installed: `pip install cvxpy numpy`
   - CVXLean framework (for using generated Lean code)

2. **Files needed:**
   ```
   cvxpy_to_lean_json.py    # CVXPY → JSON converter
   json_to_lean.py          # JSON → Lean translator  
   cvxpy_to_cvxlean.py      # Complete integration tool
   ```

## Quick Start

### Basic Usage

```python
import cvxpy as cp
from cvxpy_to_cvxlean import cvxpy_to_lean_file

# Define optimization problem in CVXPY
x = cp.Variable(name="x")
y = cp.Variable(name="y")

objective = cp.Minimize(x + 2*y)
constraints = [x >= 0, y >= 0, x + y <= 1]
problem = cp.Problem(objective, constraints)

# Convert to Lean file
cvxpy_to_lean_file(problem, "my_problem.lean", "linear_program")
```

This generates a complete Lean file:

```lean
import CvxLean

variable (x y : ℝ)

-- Optimization problem: linear_program
optimization (x y : ℝ)
  minimize (x + (2 * y))
  subject to
    c1 : 0 ≤ x
    c2 : 0 ≤ y  
    c3 : (x + y) ≤ 1
  by
    -- Use CVXLean's pre_dcp tactic to transform to DCP form
    pre_dcp
    -- Additional solving steps would go here
    sorry
```

## Core Components

### 1. CVXPY to JSON Converter (`cvxpy_to_lean_json.py`)

Converts CVXPY problems to CVXLean's EggRequest JSON format:

```python
from cvxpy_to_lean_json import problem_to_cvxlean_json

json_str = problem_to_cvxlean_json(problem, "problem_name")
```

**Output format:**
```json
{
  "request": "PerformRewrite",
  "prob_name": "problem_name", 
  "domains": [["x", ["0", "inf", "1", "1"]]],
  "target": {
    "obj_fun": "(objFun (add (var x) (var y)))",
    "constrs": [["c1", "(le 0 (var x))"]]
  }
}
```

### 2. JSON to Lean Translator (`json_to_lean.py`)

Converts S-expressions to Lean optimization syntax:

```python
from json_to_lean import json_to_lean_code

lean_code = json_to_lean_code(json_string)
```

**S-expression mapping:**
- `(add (var x) (var y))` → `(x + y)`
- `(sq (var x))` → `x ^ 2`
- `(le (var x) 5)` → `x ≤ 5`
- `(norm2 (var x))` → `‖x‖`

### 3. Complete Integration (`cvxpy_to_cvxlean.py`)

End-to-end conversion with templates:

```python
from cvxpy_to_cvxlean import cvxpy_to_lean_file

# Basic template
cvxpy_to_lean_file(problem, "basic.lean", "prob", "basic")

# With solver integration
cvxpy_to_lean_file(problem, "solver.lean", "prob", "with_solver") 

# With proof structure
cvxpy_to_lean_file(problem, "proof.lean", "prob", "with_proof")
```

## Supported CVXPY Features

### ✅ Fully Supported

- **Variables:** `cp.Variable(name="x")`, `cp.Variable(n, name="vec")`
- **Parameters:** `cp.Parameter(name="p")`
- **Arithmetic:** `+`, `-`, `*`, `/`, `^`
- **Functions:** `cp.square()`, `cp.sum_squares()`, `cp.abs()`, `cp.sqrt()`
- **Norms:** `cp.norm(x, 2)` (L2 norm)
- **Constraints:** `==`, `<=`, `>=`, `<`, `>`
- **Aggregation:** `cp.sum()`, `cp.trace()`

### ⚠️ Partial Support

- **Matrix operations:** Basic support, complex operations may need manual adjustment
- **Advanced functions:** Some functions map to generic S-expressions
- **Constraints:** Complex constraint types may require manual verification

### ❌ Not Yet Supported

- **Integer variables:** CVXPY's integer constraints
- **SDP constraints:** Semidefinite programming constraints  
- **Complex numbers:** Only real-valued problems supported

## Examples

### Linear Programming

```python
# Portfolio allocation
import numpy as np

n = 3
weights = cp.Variable(n, name="weights")
returns = np.array([0.1, 0.2, 0.15])

objective = cp.Maximize(returns.T @ weights)
constraints = [
    cp.sum(weights) == 1,
    weights >= 0,
    weights <= 0.4  # Max 40% per asset
]

problem = cp.Problem(objective, constraints)
cvxpy_to_lean_file(problem, "portfolio.lean", "portfolio_opt")
```

### Quadratic Programming

```python
# Regularized least squares
A = np.random.randn(10, 5)
b = np.random.randn(10)
x = cp.Variable(5, name="x")
lam = 0.1

objective = cp.Minimize(cp.sum_squares(A @ x - b) + lam * cp.sum_squares(x))
constraints = [x >= -1, x <= 1]

problem = cp.Problem(objective, constraints)
cvxpy_to_lean_file(problem, "lasso.lean", "regularized_ls", "with_solver")
```

### Norm Constraints

```python
# Constrained optimization with norm bounds
x = cp.Variable(3, name="x")

objective = cp.Minimize(cp.sum(x))
constraints = [
    cp.norm(x, 2) <= 1,  # L2 ball constraint
    cp.sum(x) >= 0.5
]

problem = cp.Problem(objective, constraints)
cvxpy_to_lean_file(problem, "norm_constrained.lean", "norm_problem", "with_proof")
```

## Integration with CVXLean

### Step 1: Generate Lean Code

```python
# Convert your CVXPY problem
cvxpy_to_lean_file(problem, "my_optimization.lean", "my_problem")
```

### Step 2: Add to CVXLean Project

```bash
# Copy to your CVXLean project
cp my_optimization.lean /path/to/cvxlean/project/
```

### Step 3: Use in Lean

```lean
-- Import generated file
import MyOptimization

-- The optimization problem is now available
#check my_problem

-- Solve numerically (requires solver setup)
#solve my_problem

-- Develop proofs
theorem my_problem_is_convex : convex my_problem := by
  -- Proof steps here
  sorry
```

### Step 4: Customize and Extend

- **Add solver configuration** for numerical solutions
- **Develop formal proofs** of optimality conditions  
- **Integrate with existing Lean mathematics**
- **Create reusable optimization libraries**

## Advanced Usage

### Custom Templates

Create your own templates by extending `CVXPYToCVXLeanConverter`:

```python
from cvxpy_to_cvxlean import CVXPYToCVXLeanConverter

class MyConverter(CVXPYToCVXLeanConverter):
    def _my_template(self, lean_code, prob_name, problem):
        # Add custom imports, lemmas, etc.
        return modified_lean_code

converter = MyConverter()
converter.templates['my_template'] = converter._my_template
```

### Direct JSON Processing

For advanced users who need to modify the S-expressions:

```python
import json
from cvxpy_to_lean_json import problem_to_cvxlean_json
from json_to_lean import json_to_lean_code

# Generate JSON
json_str = problem_to_cvxlean_json(problem, "my_problem")
data = json.loads(json_str)

# Modify S-expressions
data['target']['obj_fun'] = "(objFun (modified_expression))"

# Convert to Lean
modified_json = json.dumps(data)
lean_code = json_to_lean_code(modified_json)
```

### Batch Conversion

```python
problems = {
    "lp1": linear_problem_1,
    "qp1": quadratic_problem_1, 
    "portfolio": portfolio_problem
}

for name, prob in problems.items():
    cvxpy_to_lean_file(prob, f"{name}.lean", name, "with_solver")
```

## Testing and Validation

Run the comprehensive test suite:

```bash
python test_cvxpy_to_lean_json.py  # Test S-expression conversion
python demo_converter.py           # Test with examples
python example_workflow.py         # Complete workflow examples
```

## Troubleshooting

### Common Issues

1. **Missing imports in generated Lean code**
   - Ensure your CVXLean project has proper imports
   - Add required mathematical libraries

2. **Unsupported CVXPY operations**
   - Check the supported features list above
   - Consider reformulating using supported operations
   - File an issue for missing features

3. **S-expression parsing errors**
   - Validate your CVXPY problem is DCP-compliant
   - Check for unusual variable names or constraints
   - Use `problem.is_dcp()` to verify DCP compliance

4. **Lean compilation errors**
   - Verify CVXLean installation and imports
   - Check variable name conflicts
   - Ensure proper Real number typing

### Getting Help

- **File issues:** Report bugs or feature requests
- **Check examples:** See `example_workflow.py` for working patterns
- **Review generated code:** Inspect the `.lean` files for issues
- **Validate JSON:** Check the intermediate JSON for correctness

## Limitations and Future Work

### Current Limitations

- Manual integration required (no direct JSON import in CVXLean)
- Limited support for complex matrix operations
- S-expression format may not cover all CVXLean features
- Requires manual proof development

### Future Enhancements

- **Direct CVXLean integration:** JSON import functionality
- **Automated proof generation:** Basic optimality proofs
- **Expanded CVXPY support:** More functions and constraint types
- **Performance optimization:** Faster conversion for large problems
- **Interactive tools:** GUI for problem conversion and validation

## Contributing

To contribute new features or improvements:

1. **Add CVXPY support:** Extend the operator mapping in `cvxpy_to_lean_json.py`
2. **Improve Lean generation:** Enhance templates in `cvxpy_to_cvxlean.py`
3. **Add examples:** Create new workflow examples
4. **Write tests:** Add test cases for new functionality
5. **Update documentation:** Keep this README current

## License

This project extends the CVXLean framework and follows its licensing terms.

---

*For more examples and advanced usage, see the `example_workflow.py` file and generated Lean files.*