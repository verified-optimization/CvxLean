#!/usr/bin/env python3
"""
Test suite for CVXPY to CVXLean JSON converter.

Tests the conversion functionality and validates output format.
"""

import json
import unittest
import sys
import os

# Add the current directory to Python path so we can import our module
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

try:
    import numpy as np
    import cvxpy as cp
    from cvxpy_to_lean_json import (
        CVXLeanSExprEncoder, 
        CVXLeanJSONEncoder,
        problem_to_cvxlean_json
    )
    CVXPY_AVAILABLE = True
except ImportError as e:
    print(f"Warning: CVXPY not available ({e}). Some tests will be skipped.")
    CVXPY_AVAILABLE = False


class TestCVXLeanSExprEncoder(unittest.TestCase):
    """Test the S-expression encoder."""
    
    def setUp(self):
        if not CVXPY_AVAILABLE:
            self.skipTest("CVXPY not available")
        self.encoder = CVXLeanSExprEncoder()
    
    def test_variable_conversion(self):
        """Test variable conversion to S-expressions."""
        x = cp.Variable(name="x")
        result = self.encoder.expression_to_sexpr(x)
        self.assertEqual(result, "(var x)")
        
        # Test with sanitized name
        y = cp.Variable(name="y-var.test")
        result = self.encoder.expression_to_sexpr(y)
        self.assertEqual(result, "(var y_var_test)")
    
    def test_parameter_conversion(self):
        """Test parameter conversion to S-expressions."""
        p = cp.Parameter(name="param1")
        result = self.encoder.expression_to_sexpr(p)
        self.assertEqual(result, "(param param1)")
    
    def test_constant_conversion(self):
        """Test constant conversion to S-expressions."""
        # Zero constant
        zero = cp.Constant(0)
        result = self.encoder.expression_to_sexpr(zero)
        self.assertEqual(result, "0")
        
        # One constant
        one = cp.Constant(1)
        result = self.encoder.expression_to_sexpr(one)
        self.assertEqual(result, "1")
        
        # Other constant
        five = cp.Constant(5.5)
        result = self.encoder.expression_to_sexpr(five)
        self.assertEqual(result, "5.5")
    
    def test_addition_conversion(self):
        """Test addition expression conversion."""
        x = cp.Variable(name="x")
        y = cp.Variable(name="y")
        expr = x + y
        result = self.encoder.expression_to_sexpr(expr)
        self.assertEqual(result, "(add (var x) (var y))")
        
        # Test chained addition
        z = cp.Variable(name="z")
        expr = x + y + z
        result = self.encoder.expression_to_sexpr(expr)
        # Should create nested additions
        self.assertIn("add", result)
        self.assertIn("(var x)", result)
        self.assertIn("(var y)", result)
        self.assertIn("(var z)", result)
    
    def test_multiplication_conversion(self):
        """Test multiplication expression conversion."""
        x = cp.Variable(name="x")
        expr = 2 * x
        result = self.encoder.expression_to_sexpr(expr)
        self.assertIn("mul", result)
        self.assertIn("(var x)", result)
    
    def test_square_conversion(self):
        """Test square function conversion."""
        x = cp.Variable(name="x")
        expr = cp.square(x)
        result = self.encoder.expression_to_sexpr(expr)
        # Should map to sq operation
        self.assertIn("sq", result)
        self.assertIn("(var x)", result)
    
    def test_sum_squares_conversion(self):
        """Test sum_squares function conversion."""
        x = cp.Variable(2, name="x")
        expr = cp.sum_squares(x)
        result = self.encoder.expression_to_sexpr(expr)
        self.assertIn("ssq", result)
        self.assertIn("(var x)", result)
    
    def test_constraint_conversion(self):
        """Test constraint conversion to S-expressions."""
        x = cp.Variable(name="x")
        
        # Inequality constraint x >= 0
        constraint = x >= 0
        name, sexpr = self.encoder.constraint_to_sexpr(constraint)
        self.assertIn("le", sexpr)
        self.assertIn("0", sexpr)
        self.assertIn("(var x)", sexpr)
        
        # Equality constraint x == 5
        constraint = x == 5
        name, sexpr = self.encoder.constraint_to_sexpr(constraint)
        self.assertIn("eq", sexpr)
        self.assertIn("(var x)", sexpr)
        self.assertIn("5", sexpr)


class TestCVXLeanJSONEncoder(unittest.TestCase):
    """Test the complete JSON encoder."""
    
    def setUp(self):
        if not CVXPY_AVAILABLE:
            self.skipTest("CVXPY not available")
        self.encoder = CVXLeanJSONEncoder()
    
    def test_simple_problem_conversion(self):
        """Test conversion of a simple optimization problem."""
        x = cp.Variable(name="x")
        y = cp.Variable(name="y")
        
        objective = cp.Minimize(x + y)
        constraints = [x >= 0, y >= 0, x + y <= 1]
        
        problem = cp.Problem(objective, constraints)
        result = self.encoder.problem_to_cvxlean_dict(problem, "simple_test")
        
        # Check structure
        self.assertIn("request", result)
        self.assertEqual(result["request"], "PerformRewrite")
        self.assertIn("prob_name", result)
        self.assertEqual(result["prob_name"], "simple_test")
        self.assertIn("domains", result)
        self.assertIn("target", result)
        
        # Check target structure
        target = result["target"]
        self.assertIn("obj_fun", target)
        self.assertIn("constrs", target)
        
        # Check objective
        obj_fun = target["obj_fun"]
        self.assertTrue(obj_fun.startswith("(objFun"))
        self.assertIn("add", obj_fun)
        
        # Check constraints
        constrs = target["constrs"]
        self.assertIsInstance(constrs, list)
        self.assertEqual(len(constrs), 3)  # Three constraints
        
        # Each constraint should be [name, sexpr]
        for constr in constrs:
            self.assertIsInstance(constr, list)
            self.assertEqual(len(constr), 2)
            self.assertIsInstance(constr[0], str)  # name
            self.assertIsInstance(constr[1], str)  # sexpr
            self.assertTrue(constr[1].startswith("("))  # S-expression format
    
    def test_domain_extraction(self):
        """Test domain extraction from constraints."""
        x = cp.Variable(name="x")
        y = cp.Variable(name="y")
        
        # Problem with bounds
        objective = cp.Minimize(x + y)
        constraints = [x >= 0, y <= 5, x <= 10]
        
        problem = cp.Problem(objective, constraints)
        result = self.encoder.problem_to_cvxlean_dict(problem, "bounded_test")
        
        domains = result["domains"]
        self.assertIsInstance(domains, list)
        
        # Should have domains for x and y
        domain_dict = {domain[0]: domain[1] for domain in domains}
        self.assertIn("x", domain_dict)
        self.assertIn("y", domain_dict)
        
        # Each domain should be [lo, hi, lo_open, hi_open]
        for domain_name, domain_bounds in domain_dict.items():
            self.assertIsInstance(domain_bounds, list)
            self.assertEqual(len(domain_bounds), 4)


class TestEndToEndConversion(unittest.TestCase):
    """Test end-to-end conversion functionality."""
    
    def setUp(self):
        if not CVXPY_AVAILABLE:
            self.skipTest("CVXPY not available")
    
    def test_problem_to_json_string(self):
        """Test complete conversion to JSON string."""
        x = cp.Variable(name="x")
        y = cp.Variable(name="y")
        
        objective = cp.Minimize(cp.sum_squares(x) + cp.square(y))
        constraints = [x >= 0, y <= 5]
        
        problem = cp.Problem(objective, constraints)
        json_str = problem_to_cvxlean_json(problem, "test_problem")
        
        # Should be valid JSON
        parsed = json.loads(json_str)
        self.assertIsInstance(parsed, dict)
        
        # Check required fields
        self.assertIn("request", parsed)
        self.assertIn("prob_name", parsed)
        self.assertIn("domains", parsed)
        self.assertIn("target", parsed)
        
        print("Generated JSON:")
        print(json.dumps(parsed, indent=2))
    
    def test_portfolio_optimization_problem(self):
        """Test with a more realistic portfolio optimization problem."""
        n = 3  # number of assets
        mu = np.array([0.1, 0.2, 0.15])  # expected returns
        
        # Variables
        w = cp.Variable(n, name="weights")
        
        # Objective: minimize risk (we'll use a simple quadratic form)
        objective = cp.Minimize(cp.sum_squares(w))
        
        # Constraints
        constraints = [
            cp.sum(w) == 1,  # weights sum to 1
            w >= 0,          # long-only
        ]
        
        problem = cp.Problem(objective, constraints)
        json_str = problem_to_cvxlean_json(problem, "portfolio")
        
        # Should be valid JSON
        parsed = json.loads(json_str)
        self.assertIsInstance(parsed, dict)
        
        print("\nPortfolio optimization JSON:")
        print(json.dumps(parsed, indent=2))
    
    def test_quadratic_program(self):
        """Test with a quadratic programming problem."""
        x = cp.Variable(2, name="x")
        
        # Quadratic objective
        P = np.array([[2, 0.5], [0.5, 1]])
        q = np.array([1, 1])
        objective = cp.Minimize(0.5 * cp.quad_form(x, P) + q.T @ x)
        
        # Linear constraints
        A = np.array([[1, 1], [1, -1]])
        b = np.array([1, 0])
        constraints = [A @ x <= b, x >= 0]
        
        problem = cp.Problem(objective, constraints)
        json_str = problem_to_cvxlean_json(problem, "quadratic")
        
        # Should be valid JSON
        parsed = json.loads(json_str)
        self.assertIsInstance(parsed, dict)
        
        print("\nQuadratic program JSON:")
        print(json.dumps(parsed, indent=2))


def run_manual_tests():
    """Run some manual tests to see the output."""
    if not CVXPY_AVAILABLE:
        print("CVXPY not available. Skipping manual tests.")
        return
    
    print("Running manual tests...")
    print("=" * 50)
    
    # Test 1: Simple linear program
    print("\n1. Simple Linear Program:")
    x = cp.Variable(name="x")
    y = cp.Variable(name="y")
    
    objective = cp.Minimize(x + 2*y)
    constraints = [x >= 0, y >= 0, x + y <= 1]
    problem = cp.Problem(objective, constraints)
    
    json_str = problem_to_cvxlean_json(problem, "simple_lp")
    print(json_str)
    
    # Test 2: Quadratic problem
    print("\n2. Quadratic Problem:")
    x = cp.Variable(name="x")
    objective = cp.Minimize(cp.square(x - 1))
    constraints = [x >= 0, x <= 2]
    problem = cp.Problem(objective, constraints)
    
    json_str = problem_to_cvxlean_json(problem, "quadratic")
    print(json_str)
    
    # Test 3: Problem with norm
    print("\n3. Problem with L2 Norm:")
    x = cp.Variable(2, name="x")
    objective = cp.Minimize(cp.norm(x, 2))
    constraints = [cp.sum(x) == 1, x >= 0]
    problem = cp.Problem(objective, constraints)
    
    json_str = problem_to_cvxlean_json(problem, "norm_problem")
    print(json_str)


if __name__ == "__main__":
    print("CVXPY to CVXLean JSON Converter Tests")
    print("=" * 50)
    
    # Run unit tests only for now
    unittest.main(verbosity=2, exit=False)