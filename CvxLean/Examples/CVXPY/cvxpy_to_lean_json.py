#!/usr/bin/env python3
"""
CVXPY to CVXLean JSON Converter

Converts CVXPY optimization problems to CVXLean's EggRequest JSON format
for use with the Lean theorem prover's optimization framework.

Usage:
    from cvxpy_to_lean_json import problem_to_cvxlean_json
    
    # Convert problem to CVXLean JSON
    json_str = problem_to_cvxlean_json(problem, "my_problem")
"""

import json
import numpy as np
import cvxpy as cp
from typing import Dict, Any, List, Optional, Union, Tuple
import warnings
import math
import logging

# Configure logging
logger = logging.getLogger(__name__)


class CVXLeanSExprEncoder:
    """Encoder for converting CVXPY expressions to CVXLean S-expressions."""
    
    # Mapping from CVXPY operations to CVXLean operators
    OPERATOR_MAP = {
        # Arithmetic operations
        'AddExpression': 'add',
        'SubExpression': 'sub', 
        'MulExpression': 'mul',
        'DivExpression': 'div',
        'power': 'pow',
        
        # Elementwise operations
        'abs': 'abs',
        'sqrt': 'sqrt',
        'log': 'log',
        'exp': 'exp',
        'square': 'sq',
        'maximum': 'max',
        'minimum': 'min',
        
        # Norms and advanced functions
        'norm2': 'norm2',
        'quad_over_lin': 'qol',
        'geo_mean': 'geo',
        'log_sum_exp': 'lse',
        'sum_squares': 'ssq',
        'sum': 'sum',
        'trace': 'tr',
        
        # Constraint operations  
        'Equality': 'eq',
        'Inequality': 'le',
        'Zero': 'eq',
        'NonPos': 'le',
    }
    
    def __init__(self):
        self._variable_names = set()
        self._parameter_names = set()
        
    def expression_to_sexpr(self, expr) -> str:
        """Convert a CVXPY expression to S-expression string."""
        if expr is None:
            logger.warning("Encountered None expression, converting to 0")
            return "0"
            
        expr_type = expr.__class__.__name__
        logger.debug(f"Converting expression of type {expr_type}: {expr}")
        
        # Handle variables
        if isinstance(expr, cp.Variable):
            var_name = self._sanitize_name(expr.name())
            self._variable_names.add(var_name)
            return f"(var {var_name})"
            
        # Handle parameters
        elif isinstance(expr, cp.Parameter):
            param_name = self._sanitize_name(expr.name())
            self._parameter_names.add(param_name)
            return f"(param {param_name})"
            
        # Handle constants
        elif isinstance(expr, cp.Constant):
            value = expr.value
            if np.isscalar(value):
                if value == 0:
                    return "0"
                elif value == 1:
                    return "1"
                else:
                    # Use integer format for whole numbers
                    if float(value).is_integer():
                        return str(int(value))
                    else:
                        return str(float(value))
            else:
                # For non-scalar constants, we'll need more complex handling
                val = float(value.flat[0]) if hasattr(value, 'flat') else float(value)
                if val.is_integer():
                    return str(int(val))
                else:
                    return str(val)
                
        # Handle reshape operations - ignore scalar reshapes
        elif expr_type == 'reshape' or 'Reshape' in expr_type:
            # For scalar variables, just return the underlying expression
            if hasattr(expr, 'args') and len(expr.args) > 0:
                inner_expr = expr.args[0]
                # Check if it's reshaping a scalar (typically to (1,) shape)
                if hasattr(expr, 'shape') and expr.shape == (1,):
                    return self.expression_to_sexpr(inner_expr)
                elif hasattr(inner_expr, 'shape') and len(inner_expr.shape) == 0:  # scalar
                    return self.expression_to_sexpr(inner_expr)
                else:
                    # For non-scalar reshapes, we'd need more complex handling
                    return self.expression_to_sexpr(inner_expr)
            return "0"
        
        # Handle composite expressions
        else:
            return self._handle_composite_expression(expr, expr_type)
    
    def _handle_composite_expression(self, expr, expr_type: str) -> str:
        """Handle composite expressions with arguments."""
        
        # Map CVXPY type to CVXLean operator
        if expr_type in self.OPERATOR_MAP:
            op = self.OPERATOR_MAP[expr_type]
        else:
            # Try to infer operator from class name
            op = expr_type.lower().replace('expression', '')
            if not op:
                op = 'unknown'
            logger.warning(f"Unknown expression type: {expr_type}, using operator: {op}, expression: {expr}")
        
        # Get arguments
        args = []
        if hasattr(expr, 'args') and expr.args:
            args = [self.expression_to_sexpr(arg) for arg in expr.args]
        
        # Special handling for specific operations
        if expr_type == 'power':
            # Check if this is a square (power of 2)
            if len(args) == 1 and hasattr(expr, 'p'):
                try:
                    p_val = expr.p
                    # Handle case where p might be a Constant object
                    if hasattr(p_val, 'value'):
                        p_val = p_val.value
                    p_float = float(p_val)
                    if abs(p_float - 2.0) < 1e-10:
                        return f"(sq {args[0]})"
                    else:
                        power_val = int(p_float) if p_float.is_integer() else p_float
                        return f"(pow {args[0]} {power_val})"
                except:
                    # Fallback if we can't extract power value
                    return f"(pow {args[0]} 2)"
            elif len(args) == 2:
                return f"(pow {args[0]} {args[1]})"
            elif len(args) == 1:
                return f"(pow {args[0]} 2)"
        elif expr_type == 'quad_over_lin':
            # This is how CVXPY represents sum_squares internally
            if len(args) == 2:
                # Check if second arg is constant 1 (typical for sum_squares)
                if isinstance(expr.args[1], cp.Constant) and expr.args[1].value == 1:
                    return f"(ssq {args[0]})"
                else:
                    return f"(qol {args[0]} {args[1]})"
        elif expr_type == 'Pnorm':
            # Handle norms
            if hasattr(expr, 'p') and expr.p == 2:
                return f"(norm2 {args[0]})"
            else:
                return f"(pnorm {args[0]})"
        elif expr_type == 'AddExpression':
            if len(args) == 0:
                return "0"
            elif len(args) == 1:
                return args[0]
            elif len(args) == 2:
                return f"(add {args[0]} {args[1]})"
            else:
                # Chain multiple additions
                result = args[0]
                for arg in args[1:]:
                    result = f"(add {result} {arg})"
                return result
                
        elif expr_type == 'MulExpression':
            if len(args) == 2:
                return f"(mul {args[0]} {args[1]})"
            else:
                # Chain multiplications
                result = args[0] if args else "1"
                for arg in args[1:]:
                    result = f"(mul {result} {arg})"
                return result
                
        elif expr_type == 'power' and len(args) == 2:
            return f"(pow {args[0]} {args[1]})"
            
        elif expr_type == 'sum_squares':
            if len(args) == 1:
                return f"(ssq {args[0]})"
            
        elif expr_type == 'norm':
            # Check if it's L2 norm
            if hasattr(expr, 'p') and expr.p == 2:
                return f"(norm2 {args[0]})" if args else "(norm2 0)"
        
        elif expr_type == 'log_sum_exp':
            # Special handling for log_sum_exp with hstack
            if len(args) == 1 and hasattr(expr, 'args') and len(expr.args) == 1:
                # Check if the argument is an hstack
                arg_expr = expr.args[0]
                if hasattr(arg_expr, '__class__') and 'Hstack' in arg_expr.__class__.__name__:
                    # Extract the hstack arguments
                    if hasattr(arg_expr, 'args') and len(arg_expr.args) == 2:
                        # Two variables in hstack - convert to log((exp x) + (exp y))
                        var1_sexpr = self.expression_to_sexpr(arg_expr.args[0])
                        var2_sexpr = self.expression_to_sexpr(arg_expr.args[1])
                        return f"(lse {var1_sexpr} {var2_sexpr})"
            # Fallback to general log_sum_exp
            return f"(lse {args[0]})" if args else "(lse 0)"
        
        elif expr_type == 'Hstack':
            # For standalone hstack (shouldn't happen in log_sum_exp context due to above)
            if len(args) == 2:
                return f"(hstack {args[0]} {args[1]})"
            
        # Default case: apply operator to all arguments
        if len(args) == 0:
            return f"({op})"
        elif len(args) == 1:
            return f"({op} {args[0]})"
        elif len(args) == 2:
            return f"({op} {args[0]} {args[1]})"
        else:
            # For more than 2 args, we may need special handling
            args_str = " ".join(args)
            return f"({op} {args_str})"
    
    def constraint_to_sexpr(self, constraint) -> Tuple[str, str]:
        """Convert a constraint to (name, s-expression) tuple."""
        constraint_type = constraint.__class__.__name__
        
        # Generate constraint name
        constraint_name = f"{len(self._variable_names)}:{constraint_type.lower()}"
        
        if constraint_type == 'Equality' and len(constraint.args) == 2:
            lhs = self.expression_to_sexpr(constraint.args[0])
            rhs = self.expression_to_sexpr(constraint.args[1])
            sexpr = f"(eq {lhs} {rhs})"
            
        elif constraint_type in ['Inequality', 'NonPos'] and len(constraint.args) == 2:
            lhs = self.expression_to_sexpr(constraint.args[0])
            rhs = self.expression_to_sexpr(constraint.args[1])
            sexpr = f"(le {lhs} {rhs})"
            
        elif constraint_type == 'Zero' and len(constraint.args) == 1:
            expr = self.expression_to_sexpr(constraint.args[0])
            sexpr = f"(eq {expr} 0)"
            
        else:
            # Fallback for unknown constraint types
            logger.warning(f"Unsupported constraint type: {constraint_type}, constraint: {constraint}")
            if hasattr(constraint, 'args') and len(constraint.args) >= 1:
                expr = self.expression_to_sexpr(constraint.args[0])
                sexpr = f"(le {expr} 0)"
            else:
                sexpr = "(le 0 0)"  # Trivial constraint
        
        return constraint_name, sexpr
    
    def _sanitize_name(self, name: str) -> str:
        """Sanitize variable/parameter names for CVXLean."""
        if not name:
            return "unnamed"
        # Replace problematic characters
        sanitized = name.replace(" ", "_").replace("-", "_").replace(".", "_")
        # Ensure it starts with a letter or underscore
        if not (sanitized[0].isalpha() or sanitized[0] == '_'):
            sanitized = "var_" + sanitized
        return sanitized


class CVXLeanJSONEncoder:
    """Encoder for converting CVXPY problems to CVXLean EggRequest JSON format."""
    
    def __init__(self):
        self.sexpr_encoder = CVXLeanSExprEncoder()
    
    def problem_to_cvxlean_dict(self, problem: cp.Problem, prob_name: str = "problem") -> Dict[str, Any]:
        """Convert a CVXPY problem to CVXLean EggRequest dictionary."""
        
        # Convert objective
        if problem.objective is None:
            obj_sexpr = "(objFun 0)"
            obj_sense = "minimize"
        else:
            obj_expr = self.sexpr_encoder.expression_to_sexpr(problem.objective.expr)
            obj_sexpr = f"(objFun {obj_expr})"
            obj_sense = problem.objective.NAME.lower()
        
        # Convert constraints
        constraints = []
        for constraint in problem.constraints:
            name, sexpr = self.sexpr_encoder.constraint_to_sexpr(constraint)
            constraints.append([name, sexpr])
        
        # Extract domains from variables and constraints
        domains = self._extract_domains(problem)
        
        # Build the EggRequest structure
        result = {
            "request": "PerformRewrite",
            "prob_name": prob_name,
            "domains": domains,
            "target": {
                "obj_fun": obj_sexpr,
                "obj_sense": obj_sense,
                "constrs": constraints
            }
        }
        
        return result
    
    def _extract_domains(self, problem: cp.Problem) -> List[List[Union[str, List[str]]]]:
        """Extract variable domains from the problem."""
        domains = []
        
        # Get all variables from the problem
        variables = problem.variables()
        
        for var in variables:
            var_name = self.sexpr_encoder._sanitize_name(var.name())
            
            # Default domain is unbounded
            domain = ["-inf", "inf", "1", "1"]  # [lo, hi, lo_open, hi_open]
            
            # Add shape information for vector/matrix variables
            if var.shape:
                if len(var.shape) == 1:  # Vector variable
                    domain.append(f"vector_{var.shape[0]}")
                elif len(var.shape) == 2:  # Matrix variable
                    domain.append(f"matrix_{var.shape[0]}_{var.shape[1]}")
            else:  # Scalar variable
                domain.append("scalar")
            
            # Try to extract bounds from constraints
            # This is a simplified version - full implementation would need
            # more sophisticated constraint analysis
            for constraint in problem.constraints:
                domain = self._update_domain_from_constraint(domain, var, constraint)
            
            domains.append([var_name, domain])
        
        return domains
    
    def _update_domain_from_constraint(self, domain: List[str], var, constraint) -> List[str]:
        """Update variable domain based on a constraint."""
        # This is a simplified implementation
        # A full implementation would need to analyze the constraint structure
        
        if hasattr(constraint, 'args') and len(constraint.args) == 2:
            lhs, rhs = constraint.args
            
            # Check for simple bounds like x >= 0 or x <= 5
            if isinstance(lhs, cp.Variable) and lhs.id == var.id and isinstance(rhs, cp.Constant):
                if constraint.__class__.__name__ == 'Inequality':
                    # x <= rhs.value, so update upper bound
                    domain[1] = str(float(rhs.value))
                elif hasattr(constraint, 'LE_SLACK') or 'NonPos' in constraint.__class__.__name__:
                    # x >= rhs.value, so update lower bound  
                    domain[0] = str(float(rhs.value))
                    
            elif isinstance(rhs, cp.Variable) and rhs.id == var.id and isinstance(lhs, cp.Constant):
                if constraint.__class__.__name__ == 'Inequality':
                    # lhs.value <= x, so update lower bound
                    domain[0] = str(float(lhs.value))
        
        return domain


def problem_to_cvxlean_json(problem: cp.Problem, prob_name: str = "problem", indent: Optional[int] = 2) -> str:
    """
    Convert a CVXPY problem to CVXLean EggRequest JSON string.
    
    Args:
        problem: CVXPY Problem to convert
        prob_name: Name for the problem in CVXLean
        indent: JSON indentation (None for compact)
    
    Returns:
        JSON string in CVXLean EggRequest format
    """
    encoder = CVXLeanJSONEncoder()
    problem_dict = encoder.problem_to_cvxlean_dict(problem, prob_name)
    return json.dumps(problem_dict, indent=indent)


def save_problem_cvxlean_json(problem: cp.Problem, filename: str, prob_name: str = "problem", indent: Optional[int] = 2):
    """Save a CVXPY problem to a CVXLean JSON file."""
    json_str = problem_to_cvxlean_json(problem, prob_name, indent)
    with open(filename, 'w') as f:
        f.write(json_str)


if __name__ == "__main__":
    # Example usage and test
    print("CVXPY to CVXLean JSON Converter")
    print("=" * 40)
    
    # Create a test problem
    x = cp.Variable(2, name="x_vector")
    y = cp.Variable(name="y_scalar")
    
    objective = cp.Minimize(cp.sum_squares(x) + cp.square(y))
    constraints = [x >= 0, y <= 5, cp.norm(x, 2) <= 1]
    
    problem = cp.Problem(objective, constraints)
    
    print("Original problem:")
    print(problem)
    
    # Convert to CVXLean JSON
    json_str = problem_to_cvxlean_json(problem, "test_problem")
    print(f"\nCVXLean JSON:")
    print(json_str)