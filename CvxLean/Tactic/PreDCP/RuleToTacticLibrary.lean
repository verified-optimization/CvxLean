import CvxLean.Lib.Equivalence
import CvxLean.Tactic.PreDCP.RuleToTacticCmd
import CvxLean.Tactic.Arith.Arith

/-- Attempt to close the goal using the lemma specified with a combination of
`simp` and `rw`. -/
syntax "simp_or_rw" "[" Lean.Parser.Tactic.rwRule "]" : tactic

macro_rules
| `(tactic| simp_or_rw [$rule]) =>
  let symm := !rule.raw[0].isNone
  match rule.raw[1] with
  | `(term| $e:term) =>
    if symm then
      `(tactic| (try { simp only [←$e:term] } <;> repeat' (rw [←$e:term])))
    else
      `(tactic| (try { simp only [$e:term] } <;> repeat' (rw [$e:term])))

namespace CvxLean

set_option linter.unreachableTactic false

/- Objective function rules. -/

register_objFun_rule_to_tactic
    "map_objFun_log"; "(prob (objFun ?a) ?cs)" => "(prob (objFun (log ?a)) ?cs)" :=
  apply Minimization.Equivalence.map_objFun_log (by positivity!);

register_objFun_rule_to_tactic
    "map_objFun_sq"; "(prob (objFun ?a) ?cs)" => "(prob (objFun (pow ?a 2)) ?cs)" :=
  apply Minimization.Equivalence.map_objFun_sq (by positivity!);


/- Equality rules. -/

register_rule_to_tactic "log_eq_log" ; "(eq ?a ?b)" => "(eq (log ?a) (log ?b))" :=
  rw [Real.log_eq_log (by positivity!) (by positivity!)];


/- Less than or equal rules. -/

register_rule_to_tactic "le_sub_iff_add_le" ; "(le ?a (sub ?b ?c))" => "(le (add ?a ?c) ?b)" :=
  rw [le_sub_iff_add_le];

register_rule_to_tactic "le_sub_iff_add_le-rev" ; "(le (add ?a ?c) ?b)" => "(le ?a (sub ?b ?c))" :=
  rw [←le_sub_iff_add_le];

register_rule_to_tactic "sub_le_iff_le_add"; "(le (sub ?a ?c) ?b)" => "(le ?a (add ?b ?c))" :=
  rewrite [sub_le_iff_le_add];

register_rule_to_tactic "sub_le_iff_le_add-rev"; "(le ?a (add ?b ?c))" => "(le (sub ?a ?c) ?b)" :=
  rw [←sub_le_iff_le_add];

register_rule_to_tactic "div_le_iff" ; "(le (div ?a ?b) ?c)" => "(le ?a (mul ?b ?c))" :=
  rw [div_le_iff (by positivity!)];

register_rule_to_tactic "div_le_iff-rev" ; "(le (div ?a ?b) ?c)" => "(le ?a (mul ?b ?c))" :=
  rw [←div_le_iff (by positivity!)];

register_rule_to_tactic "div_le_one-rev" ; "(le ?a ?b)" => "(le (div ?a ?b) 1)" :=
  rw [←div_le_one (by positivity!)];

register_rule_to_tactic "log_le_log" ; "(le (log ?a) (log ?b))" => "(le ?a ?b)" :=
  rw [Real.log_le_log_iff (by positivity!) (by positivity!)];

register_rule_to_tactic "log_le_log-rev" ; "(le ?a ?b)" => "(le (log ?a) (log ?b))" :=
  rw [←Real.log_le_log_iff (by positivity!) (by positivity!)];

register_rule_to_tactic "pow_two_le_pow_two"; "(le (pow ?a 2) (pow ?b 2))" => "(le ?a ?b)":=
  rw [Real.pow_two_le_pow_two (by positivity!) (by positivity!)];

register_rule_to_tactic "pow_two_le_pow_two-rev"; "(le ?a ?b)" => "(le (pow ?a 2) (pow ?b 2))" :=
  rw [←Real.pow_two_le_pow_two (by positivity!) (by positivity!)];


/- Field rules. -/

register_rule_to_tactic "neg_neg" ; "(neg (neg ?a))" => "?a" :=
  simp_or_rw [neg_neg (G := ℝ)];

register_rule_to_tactic "add_zero" ; "(add ?a 0)" => "?a" :=
  simp_or_rw [add_zero];

register_rule_to_tactic "add_comm" ; "(add ?a ?b)" => "(add ?b ?a)" :=
  simp_or_rw [add_comm];

register_rule_to_tactic "add_assoc" ; "(add (add ?a ?b) ?c)" => "(add ?a (add ?b ?c))" :=
  simp_or_rw [add_assoc];

register_rule_to_tactic "sub_self" ; "(sub ?a ?a)" => "0" :=
  simp_or_rw [sub_self];

register_rule_to_tactic "one_mul" ; "(mul 1 ?a)" => "?a" :=
  simp_or_rw [one_mul];

-- Exception, we cannot find the pattern otherwise.
register_rule_to_tactic "one_mul-rev" ; "?a" => "(mul 1 ?a)" :=
  norm_num;

register_rule_to_tactic "mul_zero" ; "(mul ?a 0)" => "0" :=
  simp_or_rw [mul_zero (M₀ := ℝ)];

register_rule_to_tactic "mul_comm" ; "(mul ?a ?b)" => "(mul ?b ?a)" :=
  simp_or_rw [mul_comm];

register_rule_to_tactic "mul_assoc" ; "(mul (mul ?a ?b) ?c)" => "(mul ?a (mul ?b ?c))" :=
  simp_or_rw [mul_assoc];

register_rule_to_tactic "sub_eq_add_neg"; "(sub ?a ?b)" => "(add ?a (neg ?b))" :=
  simp_or_rw [sub_eq_add_neg (G := ℝ)];

register_rule_to_tactic "sub_eq_add_neg-rev"; "(add ?a (neg ?b))" => "(sub ?a ?b)" :=
  simp_or_rw [←sub_eq_add_neg (G := ℝ)];

register_rule_to_tactic "add_sub" ; "(add ?a (sub ?b ?c))" => "(sub (add ?a ?b) ?c)" :=
  simp_or_rw [add_sub];

register_rule_to_tactic "add_sub-rev" ; "(add ?a (sub ?b ?c))" => "(sub (add ?a ?b) ?c)" :=
  simp_or_rw [←add_sub];

register_rule_to_tactic "add_mul" ; "(mul (add ?a ?b) ?c)" => "(add (mul ?a ?c) (mul ?b ?c))" :=
  simp_or_rw [add_mul];

register_rule_to_tactic "add_mul-rev" ; "(add (mul ?a ?c) (mul ?b ?c))" => "(mul (add ?a ?b) ?c)" :=
  simp_or_rw [←add_mul];

register_rule_to_tactic "mul_add" ; "(mul ?a (add ?b ?c))" => "(add (mul ?a ?b) (mul ?a ?c))" :=
  simp_or_rw [mul_add];

register_rule_to_tactic "mul_add-rev" ; "(add (mul ?a ?b) (mul ?a ?c))" => "(mul ?a (add ?b ?c))" :=
  simp_or_rw [←mul_add];

register_rule_to_tactic "mul_sub" ; "(mul ?a (sub ?b ?c))" => "(sub (mul ?a ?b) (mul ?a ?c))" :=
  simp_or_rw [←mul_sub];

register_rule_to_tactic "mul_sub-rev" ; "(sub (mul ?a ?b) (mul ?a ?c))" => "(mul ?a (sub ?b ?c))" :=
  simp_or_rw [←mul_sub];

register_rule_to_tactic "div_one" ; "(div ?a 1)" => "?a" :=
  simp_or_rw [div_one];

register_rule_to_tactic "add_div" ; "(div (add ?a ?b) ?c)" => "(add (div ?a ?c) (div ?b ?c))" :=
  simp_or_rw [add_div];

register_rule_to_tactic "add_div-rev" ; "(add (div ?a ?c) (div ?b ?c))" => "(div (add ?a ?b) ?c)" :=
  simp_or_rw [←add_div];

register_rule_to_tactic "mul_div" ; "(mul ?a (div ?b ?c))" => "(div (mul ?a ?b) ?c)"  :=
  simp_or_rw [mul_div (G := ℝ)];

register_rule_to_tactic "mul_div-rev" ; "(div (mul ?a ?b) ?c)" => "(mul ?a (div ?b ?c))" :=
  simp_or_rw [←mul_div (G := ℝ)];

register_rule_to_tactic "div_mul" ; "(mul (div ?a ?b) ?c)" => "(div ?a (div ?b ?c))" :=
  simp_or_rw [div_mul];

register_rule_to_tactic "div_mul-rev" ; "(div ?a (div ?b ?c))" => "(mul (div ?a ?b) ?c)" :=
  simp_or_rw [←div_mul];

register_rule_to_tactic "mul_div_mul_left" ; "(div (mul ?c ?a) (mul ?c ?b))" => "(div ?a ?b)" :=
  simp_or_rw [mul_div_mul_left (G₀ := ℝ) _ _ (by positivity!)];

register_rule_to_tactic "div_div" ; "(div (div ?a ?b) ?c)" => "(div ?a (mul ?b ?c))" :=
  simp_or_rw [div_div];

register_rule_to_tactic "div_div-rev" ; "(div ?a (mul ?b ?c))" => "(div (div ?a ?b) ?c)" :=
  simp_or_rw [←div_div];

register_rule_to_tactic "div_self" ; "(div ?a ?a)" => "1" :=
  simp_or_rw [div_self (G₀ := ℝ) (by positivity!)];

register_rule_to_tactic "inv_eq_one_div" ; "(inv ?a)" => "(div 1 ?a)" :=
  simp_or_rw [inv_eq_one_div (G := ℝ)];

register_rule_to_tactic "inv_inv" ; "(inv (inv ?a))" => "?a" :=
  simp_or_rw [inv_inv];


/- Power and square root rules. -/

register_rule_to_tactic "one_pow"; "(pow 1 ?a)" => "1" :=
  simp_or_rw [Real.one_rpow];

register_rule_to_tactic "pow_one"; "(pow ?a 1)" => "?a" :=
  simp_or_rw [Real.rpow_one];

register_rule_to_tactic "pow_add"; "(pow ?a (add ?b ?c))" => "(mul (pow ?a ?b) (pow ?a ?c))" :=
  simp_or_rw [Real.rpow_add (by positivity!)];

register_rule_to_tactic "pow_add-rev"; "(mul (pow ?a ?b) (pow ?a ?c))" => "(pow ?a (add ?b ?c))" :=
  simp_or_rw [←Real.rpow_add (by positivity!)];

register_rule_to_tactic "mul_pow"; "(mul (pow ?a ?n) (pow ?b ?n))" => "(pow (mul ?a ?b) ?n)" :=
  simp_or_rw [Real.mul_rpow (by positivity!) (by positivity!)];

register_rule_to_tactic "mul_pow-rev"; "(mul (pow ?a ?n) (pow ?b ?n))" => "(pow (mul ?a ?b) ?n)" :=
  simp_or_rw [←Real.mul_rpow (by positivity!) (by positivity!)];

register_rule_to_tactic "pow_mul"; "(pow ?a (mul ?n ?m))" => "(pow (pow ?a ?n) ?m)" :=
  simp_or_rw [Real.rpow_mul (by positivity!)];

register_rule_to_tactic "pow_mul-rev"; "(pow (pow ?a ?n) ?m)" => "(pow ?a (mul ?n ?m))" :=
  simp_or_rw [←Real.rpow_mul (by positivity!)];

register_rule_to_tactic "div_pow"; "(pow (div ?a ?b) ?n)" => "(div (pow ?a ?n) (pow ?b ?n))" :=
  simp_or_rw [Real.div_rpow (by positivity!) (by positivity!)];

register_rule_to_tactic "div_pow-rev"; "(div (pow ?a ?n) (pow ?b ?n))" => "(pow (div ?a ?b) ?n)" :=
  simp_or_rw [←Real.div_rpow (by positivity!) (by positivity!)];

register_rule_to_tactic "pow_sub"; "(pow ?a (sub ?b ?c))" => "(div (pow ?a ?b) (pow ?a ?c))" :=
  simp_or_rw [Real.rpow_sub (by positivity!)];

register_rule_to_tactic "pow_sub-rev"; "(div (pow ?a ?b) (pow ?a ?c))" => "(pow ?a (sub ?b ?c))" :=
  simp_or_rw [←Real.rpow_sub (by positivity!)];

register_rule_to_tactic
    "div_pow_eq_mul_pow_neg" ; "(div ?a (pow ?b ?c))" => "(mul ?a (pow ?b (neg ?c)))" :=
  simp_or_rw [Real.div_pow_eq_mul_pow_neg (by positivity!)];

register_rule_to_tactic
    "div_pow_eq_mul_pow_neg-rev" ; "(div ?a (pow ?b ?c))" => "(mul ?a (pow ?b (neg ?c)))" :=
  simp_or_rw [←Real.div_pow_eq_mul_pow_neg (by positivity!)];

register_rule_to_tactic "one_div_eq_pow_neg_one"; "(div 1 ?a)" => "(pow ?a (neg 1))" :=
  simp_or_rw [Real.one_div_eq_pow_neg_one (by positivity!)];

register_rule_to_tactic "sqrt_eq_rpow" ; "(sqrt ?a)" => "(pow ?a 0.5)" :=
  simp_or_rw [Real.sqrt_eq_rpow];

register_rule_to_tactic "sqrt_eq_rpow-rev" ; "(pow ?a 0.5)" => "(sqrt ?a)" :=
  simp_or_rw [←Real.sqrt_eq_rpow];

register_rule_to_tactic "sqrt_mul" ; "(sqrt (mul ?a ?b))" => "(mul (sqrt ?a) (sqrt ?b))" :=
  simp_or_rw [Real.sqrt_mul (by positivity!)];

register_rule_to_tactic "sqrt_mul-rev" ; "(mul (sqrt ?a) (sqrt ?b))" => "(sqrt (mul ?a ?b))" :=
  simp_or_rw [←Real.sqrt_mul (by positivity!)];

register_rule_to_tactic "pow_two"; "(pow ?a 2)" => "(mul ?a ?a)" :=
  (norm_cast; simp_or_rw [pow_two]);

register_rule_to_tactic "pow_two-rev"; "(mul ?a ?a)" => "(pow ?a 2)" :=
  (norm_cast; simp_or_rw [←pow_two]);

register_rule_to_tactic "pow_half_two"; "(pow (pow ?a 0.5) 2)" => "?a" :=
  simp_or_rw [Real.pow_half_two (by positivity!)];

-- Exception, technically ← but we cannot find the pattern otherwise.
register_rule_to_tactic "pow_half_two-rev"; "?a" => "(pow (pow ?a 0.5) 2)" :=
  simp_or_rw [Real.pow_half_two (by positivity!)];

register_rule_to_tactic "binomial_two";
    "(pow (add ?a ?b) 2)" => "(add (pow ?a 2) (add (mul 2 (mul ?a ?b)) (pow ?b 2)))" :=
  simp_or_rw [Real.binomial_two];

register_rule_to_tactic "rpow_eq_mul_rpow_pred"; "(pow ?a ?b)" => "(mul ?a (pow ?a (sub ?b 1)))" :=
  simp_or_rw [Real.rpow_eq_mul_rpow_pred (by positivity!)];

register_rule_to_tactic "inv_eq_pow_neg_one"; "(inv ?a)" => "(pow ?a (neg 1))" :=
  simp_or_rw [Real.inv_eq_pow_neg_one (by positivity!)];


/- Exponential and logarithm rules. -/

register_rule_to_tactic "exp_add" ; "(exp (add ?a ?b))" => "(mul (exp ?a) (exp ?b))" :=
  simp_or_rw [Real.exp_add];

register_rule_to_tactic "exp_add-rev" ; "(mul (exp ?a) (exp ?b))" => "(exp (add ?a ?b))" :=
  simp_or_rw [←Real.exp_add];

register_rule_to_tactic "exp_sub" ; "(exp (sub ?a ?b))" => "(div (exp ?a) (exp ?b))" :=
  simp_or_rw [Real.exp_sub];

register_rule_to_tactic "exp_sub-rev" ; "(div (exp ?a) (exp ?b))" => "(exp (sub ?a ?b))" :=
  simp_or_rw [←Real.exp_sub];

register_rule_to_tactic "exp_mul" ; "(exp (mul ?a ?b))" => "(pow (exp ?a) ?b)" :=
  simp_or_rw [Real.exp_mul];

register_rule_to_tactic "exp_mul-rev" ; "(pow (exp ?a) ?b)" => "(exp (mul ?a ?b))" :=
  simp_or_rw [←Real.exp_mul];

register_rule_to_tactic "exp_neg_eq_one_div"; "(exp (neg ?a))" => "(div 1 (exp ?a))" :=
  simp_or_rw [Real.exp_neg_eq_one_div];

register_rule_to_tactic "exp_neg_eq_one_div-rev" ; "(div 1 (exp ?a))" => "(exp (neg ?a))" :=
  simp_or_rw [←Real.exp_neg_eq_one_div];

register_rule_to_tactic "log_mul" ; "(log (mul ?a ?b))" => "(add (log ?a) (log ?b))" :=
  simp_or_rw [Real.log_mul (by positivity!) (by positivity!)];

register_rule_to_tactic "log_mul-rev"; "(add (log ?a) (log ?b))" => "(log (mul ?a ?b))" :=
  simp_or_rw [←Real.log_mul (by positivity!) (by positivity!)];

register_rule_to_tactic "log_div" ; "(log (div ?a ?b))" => "(sub (log ?a) (log ?b))" :=
  simp_or_rw [Real.log_div (by positivity!) (by positivity!)];

register_rule_to_tactic "log_div-rev"; "(sub (log ?a) (log ?b))" => "(log (div ?a ?b))" :=
  simp_or_rw [←Real.log_div (by positivity!) (by positivity!)];

register_rule_to_tactic "log_pow" ; "(log (pow ?a ?b))" => "(mul ?b (log ?a))" :=
  simp_or_rw [Real.log_rpow (by positivity!)];

register_rule_to_tactic "log_pow-rev" ; "(mul ?b (log ?a))" => "(log (pow ?a ?b))" :=
  simp_or_rw [←Real.log_rpow (by positivity!)];

-- Special type of rule as it only works if the exponent is a natural number.
register_rule_to_tactic "log_pow_nat" ; "(log (pow ?a ?b))" => "(mul ?b (log ?a))" :=
  (norm_cast; simp_or_rw [Real.log_pow]);

register_rule_to_tactic "log_pow_nat-rev" ; "(mul ?b (log ?a))" => "(log (pow ?a ?b))" :=
  (norm_cast; simp_or_rw [←Real.log_pow]);

register_rule_to_tactic "exp_log" ; "(exp (log ?a))" => "?a" :=
  simp_or_rw [Real.exp_log (by positivity!)];

register_rule_to_tactic "log_exp" ; "(log (exp ?a))" => "?a" :=
  simp_or_rw [Real.log_exp];


/- Absolute value rules. -/

register_rule_to_tactic "abs_nonneg" ; "(abs ?a)" => "?a" :=
  simp_or_rw [abs_eq_self.mpr (by positivity!)];

register_rule_to_tactic "abs_nonpos" ; "(abs ?a)" => "(neg ?a)" :=
  simp_or_rw [abs_eq_neg_self.mpr (by linarith)];


/- Min and max rules. -/

register_rule_to_tactic "min_eq_left"; "(min ?a ?b)" => "?a" :=
  simp_or_rw [min_eq_left (by linarith)];

register_rule_to_tactic "min_eq_right"; "(min ?a ?b)" => "?b" :=
  simp_or_rw [min_eq_right (by linarith)];

register_rule_to_tactic "max_eq_left"; "(max ?a ?b)" => "?a" :=
  simp_or_rw [max_eq_left (by linarith)];

register_rule_to_tactic "max_eq_right"; "(max ?a ?b)" => "?b" :=
  simp_or_rw [max_eq_right (by linarith)];


/- Atom folding. -/

register_rule_to_tactic "xexp_fold"; "(mul ?a (exp ?a))" => "(xexp ?a)" :=
  rfl;

register_rule_to_tactic "xexp_unfold"; "(xexp ?a)" => "(mul ?a (exp ?a))" :=
  rfl;

register_rule_to_tactic "entr_fold"; "(neg (mul ?a (log ?a)))" => "(entr ?a)" :=
  rfl;

register_rule_to_tactic "entr_unfold"; "(entr ?a)" => "(neg (mul ?a (log ?a)))" :=
  rfl;

register_rule_to_tactic "qol_fold"; "(div (pow ?a 2) ?b)" => "(qol ?a ?b)" :=
  rfl;

register_rule_to_tactic "qol_unfold"; "(qol ?a ?b)" => "(div (pow ?a 2) ?b)" :=
  rfl;

register_rule_to_tactic "geo_fold"; "(sqrt (mul ?a ?b))" => "(geo ?a ?b)" :=
  rfl;

register_rule_to_tactic "geo_unfold"; "(geo ?a ?b)" => "(sqrt (mul ?a ?b))" :=
  rfl;

register_rule_to_tactic "lse_fold"; "(log (add (exp ?a) (exp ?b)))" => "(lse ?a ?b)" :=
  rfl;

register_rule_to_tactic "lse_unfold"; "(lse ?a ?b)" => "(log (add (exp ?a) (exp ?b)))" :=
  rfl;

register_rule_to_tactic "norm2_fold"; "(sqrt (add (pow ?a 2) (pow ?b 2)))" => "(norm2 ?a ?b)" :=
  rfl;

register_rule_to_tactic "norm2_unfold"; "(norm2 ?a ?b)" => "(sqrt (add (pow ?a 2) (pow ?b 2)))" :=
  rfl;

end CvxLean
