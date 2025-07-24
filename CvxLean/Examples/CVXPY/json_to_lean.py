#!/usr/bin/env python3
"""
JSON S-expression to Lean Syntax Translator

Generates proper CVXLean syntax that matches the framework.
"""

import json
import re
from typing import Dict, Any, List, Set, Tuple, Optional


class SExprToLeanTranslator:
    """Translates S-expressions to proper CVXLean Lean syntax."""
    
    def __init__(self):
        self.variable_names = set()
        self.parameter_names = set()
        
        # Updated mapping for actual CVXLean operators
        self.operator_map = {
            'add': '+',
            'sub': '-', 
            'mul': '*',
            'div': '/',
            'pow': '^',
            'neg': '-',
            'abs': 'abs',
            'sqrt': 'sqrt',
            'log': 'log',
            'exp': 'exp',
            'sq': '^ 2',  # Square operation
            'ssq': 'sum_squares',  # Sum of squares (CVXLean function)
            'norm2': 'norm₂',  # L2 norm
            'max': 'max',
            'min': 'min',
            'sum': 'sum',
            'tr': 'trace',
            
            # Advanced functions - use mathematical expressions that CvxLean recognizes
            'lse': 'log_sum_exp',  # Will be handled specially
            'logSumExp₂': 'log_sum_exp_2',  # Will be handled specially
            
            # Constraint operators
            'eq': '=',
            'le': '≤',
            'ge': '≥',
            'lt': '<',
            'gt': '>'
        }
    
    def parse_sexpr(self, sexpr: str) -> Any:
        """Parse S-expression string into a nested structure."""
        sexpr = sexpr.strip()
        
        if not sexpr:
            return ""
            
        if not sexpr.startswith('('):
            # Atomic expression (number, variable name, etc.)
            try:
                # Try to parse as number
                if '.' in sexpr:
                    return float(sexpr)
                else:
                    return int(sexpr)
            except ValueError:
                return sexpr
        
        # Parse nested S-expression
        tokens = self._tokenize_sexpr(sexpr)
        return self._parse_tokens(tokens)
    
    def _tokenize_sexpr(self, sexpr: str) -> List[str]:
        """Tokenize S-expression into list of tokens."""
        tokens = []
        i = 0
        while i < len(sexpr):
            char = sexpr[i]
            if char in '()':
                tokens.append(char)
                i += 1
            elif char.isspace():
                i += 1
            else:
                # Read token until space or parenthesis
                token = ""
                while i < len(sexpr) and sexpr[i] not in '() \t\n':
                    token += sexpr[i]
                    i += 1
                if token:
                    tokens.append(token)
        return tokens
    
    def _parse_tokens(self, tokens: List[str]) -> Any:
        """Parse tokenized S-expression."""
        if not tokens:
            return []
            
        if tokens[0] != '(':
            # Single token
            token = tokens[0]
            try:
                if '.' in token:
                    return float(token)
                else:
                    return int(token)
            except ValueError:
                return token
        
        # Parse list starting with '('
        result = []
        i = 1  # Skip opening paren
        while i < len(tokens) and tokens[i] != ')':
            if tokens[i] == '(':
                # Find matching closing paren
                paren_count = 1
                j = i + 1
                while j < len(tokens) and paren_count > 0:
                    if tokens[j] == '(':
                        paren_count += 1
                    elif tokens[j] == ')':
                        paren_count -= 1
                    j += 1
                # Recursively parse sub-expression
                sub_expr = self._parse_tokens(tokens[i:j])
                result.append(sub_expr)
                i = j
            else:
                # Single token
                token = tokens[i]
                try:
                    if '.' in token:
                        result.append(float(token))
                    else:
                        result.append(int(token))
                except ValueError:
                    result.append(token)
                i += 1
        
        return result
    
    def sexpr_to_lean(self, sexpr: str) -> str:
        """Convert S-expression to proper CVXLean Lean syntax."""
        parsed = self.parse_sexpr(sexpr)
        return self._translate_parsed(parsed)
    
    def _translate_parsed(self, parsed: Any) -> str:
        """Translate parsed S-expression to CVXLean Lean syntax."""
        if isinstance(parsed, (int, float)):
            if isinstance(parsed, float) and parsed.is_integer():
                return str(int(parsed))
            return str(parsed)
        
        if isinstance(parsed, str):
            return parsed
        
        if not isinstance(parsed, list) or len(parsed) == 0:
            return "0"
        
        op = parsed[0]
        args = parsed[1:] if len(parsed) > 1 else []
        
        # Handle special cases
        if op == 'var':
            if len(args) >= 1:
                var_name = str(args[0])
                self.variable_names.add(var_name)
                return var_name
            return "x"
        
        elif op == 'param':
            if len(args) >= 1:
                param_name = str(args[0])
                self.parameter_names.add(param_name)
                return param_name
            return "p"
        
        elif op == 'objFun':
            if len(args) >= 1:
                return self._translate_parsed(args[0])
            return "0"
        
        # Binary operators
        elif op in ['add', 'sub', 'mul', 'div']:
            if len(args) == 2:
                left = self._translate_parsed(args[0])
                right = self._translate_parsed(args[1])
                lean_op = self.operator_map[op]
                
                # Handle special cases for better readability
                if op == 'mul' and self._is_simple_number(args[0]):
                    return f"{left} * {right}"
                elif op == 'mul' and self._is_simple_number(args[1]):
                    return f"{left} * {right}"
                else:
                    return f"({left} {lean_op} {right})"
            elif len(args) > 2:
                # Chain operations (left-associative)
                result = self._translate_parsed(args[0])
                lean_op = self.operator_map[op]
                for arg in args[1:]:
                    arg_str = self._translate_parsed(arg)
                    result = f"({result} {lean_op} {arg_str})"
                return result
            elif len(args) == 1:
                return self._translate_parsed(args[0])
            return "0"
        
        # Unary operators
        elif op == 'neg':
            if len(args) >= 1:
                arg_str = self._translate_parsed(args[0])
                return f"(-{arg_str})"
            return "0"
        
        elif op == 'sq':
            if len(args) >= 1:
                arg_str = self._translate_parsed(args[0])
                return f"({arg_str}) ^ 2"
            return "0"
        
        elif op == 'pow':
            if len(args) >= 2:
                base = self._translate_parsed(args[0])
                exp = self._translate_parsed(args[1])
                # Parenthesize negative exponents for proper Lean syntax
                if exp.startswith('-'):
                    exp = f"({exp})"
                return f"(({base}) ^ {exp})"
            return "0"
        
        elif op in ['abs', 'sqrt', 'log', 'exp']:
            if len(args) >= 1:
                arg_str = self._translate_parsed(args[0])
                func_name = self.operator_map[op]
                return f"{func_name} ({arg_str})"
            return "0"
        
        # Special CVXLean functions
        elif op == 'ssq':
            if len(args) >= 1:
                arg_str = self._translate_parsed(args[0])
                # For vectors, use Vec.sum with vector squaring
                return f"Vec.sum ({arg_str} ^ 2)"
            return "0"
        
        elif op == 'norm2':
            if len(args) >= 1:
                arg_str = self._translate_parsed(args[0])
                return f"norm₂ ({arg_str})"
            return "0"
        
        elif op == 'sum':
            if len(args) >= 1:
                arg_str = self._translate_parsed(args[0])
                # For vectors, use Vec.sum
                return f"Vec.sum {arg_str}"
            return "0"
        
        # Special handling for log-sum-exp functions
        elif op == 'lse' or op == 'logSumExp₂':
            if len(args) == 2:
                # Two-argument log-sum-exp: log(exp(x) + exp(y))
                arg1 = self._translate_parsed(args[0])
                arg2 = self._translate_parsed(args[1])
                return f"log ((exp {arg1}) + (exp {arg2}))"
            elif len(args) >= 1:
                # General log-sum-exp for vectors (if we support it later)
                arg_str = self._translate_parsed(args[0])
                return f"log (Vec.sum (Vec.exp {arg_str}))"
            return "0"
        
        # Constraint operators
        elif op in ['eq', 'le', 'ge', 'lt', 'gt']:
            if len(args) >= 2:
                left = self._translate_parsed(args[0])
                right = self._translate_parsed(args[1])
                lean_op = self.operator_map[op]
                
                # Check if this is a vector inequality (scalar compared to vector)
                if ((left.isdigit() or left in ['0', '1']) and right.startswith('weights')) or \
                   ((right.isdigit() or right in ['0', '1']) and left.startswith('weights')):
                    # Extract variable name for vector constraints
                    var_part = right if right.startswith('weights') else left
                    scalar_part = left if var_part == right else right
                    
                    var_name = var_part.strip()
                    if var_name in self.variable_names:
                        # This is likely a vector constraint
                        if left == scalar_part:  # scalar ≤ vector → ∀ i, scalar ≤ vector i
                            return f"∀ i, {scalar_part} {lean_op} {var_name} i"
                        else:  # vector ≤ scalar → ∀ i, vector i ≤ scalar
                            return f"∀ i, {var_name} i {lean_op} {scalar_part}"
                
                return f"{left} {lean_op} {right}"
            return "true"  # Trivial constraint
        
        # Fallback: function call syntax
        else:
            # Handle multiply as an alias for mul
            if op == 'multiply':
                if len(args) == 2:
                    left = self._translate_parsed(args[0])
                    right = self._translate_parsed(args[1])
                    return f"{left} * {right}"
            
            if len(args) == 0:
                return op
            elif len(args) == 1:
                arg_str = self._translate_parsed(args[0])
                return f"{op} {arg_str}"
            else:
                args_str = " ".join(self._translate_parsed(arg) for arg in args)
                return f"{op} ({args_str})"
    
    def _is_simple_number(self, parsed_arg) -> bool:
        """Check if parsed argument is a simple number."""
        return isinstance(parsed_arg, (int, float))


class JSONToLeanConverter:
    """Converts CVXLean JSON to proper CVXLean Lean optimization syntax."""
    
    def __init__(self):
        self.translator = SExprToLeanTranslator()
    
    def convert_json_to_lean(self, json_str: str) -> str:
        """Convert JSON string to proper CVXLean optimization definition."""
        try:
            data = json.loads(json_str)
        except json.JSONDecodeError as e:
            raise ValueError(f"Invalid JSON: {e}")
        
        if not isinstance(data, dict):
            raise ValueError("JSON must be an object")
        
        # Extract problem components
        prob_name = data.get("prob_name", "optimization_problem")
        domains = data.get("domains", [])
        target = data.get("target", {})
        
        obj_fun = target.get("obj_fun", "(objFun 0)")
        obj_sense = target.get("obj_sense", "minimize")
        constrs = target.get("constrs", [])
        
        # Generate proper CVXLean code
        return self._generate_cvxlean_code(prob_name, domains, obj_fun, obj_sense, constrs)
    
    def _generate_cvxlean_code(self, prob_name: str, domains: List, obj_fun: str, obj_sense: str, constrs: List) -> str:
        """Generate proper CVXLean optimization definition."""
        
        # Clear translator state
        self.translator.variable_names.clear()
        self.translator.parameter_names.clear()
        
        # Parse objective to collect variables
        obj_lean = self.translator.sexpr_to_lean(obj_fun)
        # Add type annotation for objectives that use Vec.sum, summation, or simple expressions
        if "Vec.sum" in obj_lean or "∑" in obj_lean or not obj_lean.startswith("(") or "^" in obj_lean:
            obj_lean = f"({obj_lean} : ℝ)"
        
        # Parse constraints to collect more variables
        constraint_lines = []
        for i, (constr_name, constr_sexpr) in enumerate(constrs):
            constr_lean = self.translator.sexpr_to_lean(constr_sexpr)
            # Generate unique constraint names
            clean_name = f"c{i+1}"
            constraint_lines.append(f"      {clean_name} : {constr_lean}")
        
        # Get variable information 
        variables = sorted(self.translator.variable_names)
        parameters = sorted(self.translator.parameter_names)
        
        # Extract variable type information from domains
        var_types = {}
        for domain_info in domains:
            var_name = domain_info[0]
            domain_data = domain_info[1]
            if len(domain_data) > 4:  # Has shape info
                shape_info = domain_data[4]
                if shape_info.startswith("vector_"):
                    size = shape_info.split("_")[1]
                    var_types[var_name] = f"Fin {size} → ℝ"
                elif shape_info.startswith("matrix_"):
                    parts = shape_info.split("_")
                    rows, cols = parts[1], parts[2]
                    var_types[var_name] = f"Matrix (Fin {rows}) (Fin {cols}) ℝ"
                else:  # scalar
                    var_types[var_name] = "ℝ"
            else:  # Default to scalar
                var_types[var_name] = "ℝ"
        
        # Build proper CVXLean code
        lines = []
        
        # Add imports and setup
        lines.append("import CvxLean")
        lines.append("")
        lines.append("noncomputable section")
        lines.append("")
        lines.append("open CvxLean Minimization Real BigOperators")
        lines.append("")
        
        # Create the optimization definition (proper CVXLean style)
        if variables:
            var_decl = " ".join(f"({var} : {var_types.get(var, 'ℝ')})" for var in variables)
            lines.append(f"def {prob_name} :=")
            lines.append(f"  optimization {var_decl}")
        else:
            lines.append(f"def {prob_name} :=")
            lines.append("  optimization")
        
        lines.append(f"    {obj_sense} {obj_lean}")
        
        if constraint_lines:
            lines.append("    subject to")
            lines.extend(constraint_lines)
        
        lines.append("")
        lines.append("-- Solve the problem directly (applies pre_dcp automatically)")
        lines.append(f"solve {prob_name}")
        lines.append("")
        lines.append("-- Check the results")
        lines.append(f"#eval {prob_name}.status")
        lines.append(f"#eval {prob_name}.solution")
        lines.append(f"#eval {prob_name}.value")
        lines.append("")
        lines.append("end")
        
        return "\n".join(lines)


def json_to_lean_code(json_str: str) -> str:
    """
    Convert CVXLean JSON to proper CVXLean Lean code.
    
    Args:
        json_str: JSON string from cvxpy_to_lean_json converter
        
    Returns:
        Proper CVXLean optimization definition
    """
    converter = JSONToLeanConverter()
    return converter.convert_json_to_lean(json_str)


if __name__ == "__main__":
    # Test with the example that was failing
    example_json = '''
    {
      "request": "PerformRewrite",
      "prob_name": "quadratic_example",
      "domains": [
        ["x", ["0", "2", "1", "1"]]
      ],
      "target": {
        "obj_fun": "(objFun (ssq (add (var x) (neg 1))))",
        "constrs": [
          ["c1", "(le 0 (var x))"],
          ["c2", "(le (var x) 2)"]
        ]
      }
    }
    '''
    
    try:
        lean_code = fixed_json_to_lean_code(example_json)
        print("Generated proper CVXLean code:")
        print("-" * 50)
        print(lean_code)
    except Exception as e:
        print(f"Error: {e}")