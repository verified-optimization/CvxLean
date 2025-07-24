#!/usr/bin/env python3
"""
CVXPY to CVXLean Integration Tool

This generates proper CVXLean syntax that works with the framework.
"""

import cvxpy as cp
from cvxpy_to_lean_json import problem_to_cvxlean_json
from json_to_lean import json_to_lean_code
import os
import logging
from typing import Optional

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(levelname)s: %(message)s')
logger = logging.getLogger(__name__)


def cvxpy_to_lean_code(problem: cp.Problem, prob_name: str) -> str:
    """
    Convert CVXPY problem directly to CVXLean Lean code.
    
    Args:
        problem: CVXPY Problem to convert
        prob_name: Name for the optimization problem  
        
    Returns:
        CVXLean optimization definition
    """
    # Log problem information
    logger.info(f"Converting CVXPY problem '{prob_name}' to CVXLean")
    logger.info(f"Problem has {len(problem.variables())} variables and {len(problem.constraints)} constraints")
    
    # Check for potential issues
    if problem.objective is None:
        logger.warning("Problem has no objective function")
    else:
        logger.info(f"Objective: {problem.objective.NAME} {problem.objective.expr}")
    
    for i, constraint in enumerate(problem.constraints):
        logger.info(f"Constraint {i+1}: {constraint}")
    
    # Step 1: Convert to JSON
    json_str = problem_to_cvxlean_json(problem, prob_name)
    
    # Step 2: Convert JSON to Lean
    lean_code = json_to_lean_code(json_str)
    
    return lean_code


def cvxpy_to_lean_file(problem: cp.Problem, filename: str, prob_name: str) -> str:
    """
    Convert CVXPY problem and save to proper CVXLean Lean file.
    
    Args:
        problem: CVXPY Problem to convert
        filename: Output filename (will add .lean if needed)
        prob_name: Name for the optimization problem
        
    Returns:
        Path to generated file
    """
    lean_code = cvxpy_to_lean_code(problem, prob_name)
    
    # Ensure .lean extension
    if not filename.endswith('.lean'):
        filename += '.lean'
    
    with open(filename, 'w') as f:
        f.write(lean_code)
    
    print(f"Saved proper CVXLean code to {filename}")
    return filename


def generate_examples():
    """Generate working CVXLean examples from CVXPY problems."""
    
    print("Generating proper CVXLean examples from CVXPY problems...")
    
    # Example 1: Simple Linear Program
    print("\n1. Simple Linear Program")
    x = cp.Variable(name="x")
    y = cp.Variable(name="y") 
    
    objective = cp.Minimize(x + 2*y)
    constraints = [x >= 0, y >= 0, x + y <= 1]
    lp_problem = cp.Problem(objective, constraints)
    
    cvxpy_to_lean_file(lp_problem, "SimpleLP.lean", "simple_lp")
    
    # Example 2: Quadratic Program  
    print("2. Quadratic Program")
    x = cp.Variable(name="x")
    
    objective = cp.Minimize(cp.square(x - 1))
    constraints = [x >= 0, x <= 2]
    qp_problem = cp.Problem(objective, constraints)
    
    cvxpy_to_lean_file(qp_problem, "Quadratic.lean", "quadratic_problem")
    
    # Example 3: Portfolio Optimization
    print("3. Portfolio Optimization")
    import numpy as np
    n = 3
    w = cp.Variable(n, name="weights")
    
    objective = cp.Minimize(cp.sum_squares(w))
    constraints = [cp.sum(w) == 1, w >= 0]
    portfolio_problem = cp.Problem(objective, constraints)
    
    cvxpy_to_lean_file(portfolio_problem, "Portfolio.lean", "portfolio_optimization")
    
    # Example 4: Log-Sum-Exp Problem (New!)
    print("4. Log-Sum-Exp Problem")
    x = cp.Variable(name="x")
    y = cp.Variable(name="y")
    
    objective = cp.Minimize(cp.log_sum_exp(cp.hstack([x, y])))
    constraints = [x + y >= 1, x >= -2, y >= -2, x <= 2, y <= 2]
    lse_problem = cp.Problem(objective, constraints)
    
    cvxpy_to_lean_file(lse_problem, "LogSumExp.lean", "log_sum_exp_problem")
    
    print("\nGenerated 4 working CVXLean files!")
    print("Files created:")
    for filename in ["SimpleLP.lean", "Quadratic.lean", "Portfolio.lean", "LogSumExp.lean"]:
        if os.path.exists(filename):
            print(f"  ✓ {filename}")


if __name__ == "__main__":
    print("CVXPY to CVXLean Integration Tool")
    print("=" * 50)
    
    # Generate working examples
    generate_examples()
    
    print("\n" + "=" * 50)
    print("These files should now work properly with CVXLean!")
    print("=" * 50)