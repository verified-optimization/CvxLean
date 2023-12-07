import CvxLean.Tactic.Convexify.RewriteMapCmd
import CvxLean.Tactic.Convexify.Basic
import CvxLean.Tactic.Arith.Arith

-- TODO: Move.
lemma Real.log_eq_log {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : Real.log x = Real.log y ↔ x = y :=
  ⟨fun h => by
    have hxmem := Set.mem_Ioi.2 hx
    have hymem := Set.mem_Ioi.2 hy
    have heq : Set.restrict (Set.Ioi 0) log ⟨x, hxmem⟩ =
      Set.restrict (Set.Ioi 0) log ⟨y, hymem⟩ := by
      simp [h]
    have h := Real.log_injOn_pos.injective heq
    simp [Subtype.eq] at h
    exact h,
  fun h => by rw [h]⟩

-- TODO: Move.
lemma Real.div_pow_eq_mul_pow_neg {a b c : ℝ} (hb : 0 ≤ b) : a / (b ^ c) = a * b ^ (-c) := by
  rw [div_eq_mul_inv, ←rpow_neg hb]

-- TODO: Move.
lemma Real.one_div_eq_pow_neg_one {a : ℝ} (ha : 0 < a) : 1 / a = a ^ (-1) := by
  rw [Real.rpow_neg (le_of_lt ha), rpow_one, div_eq_mul_inv, one_mul]

-- TODO: Move.
lemma Real.pow_half_two {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 2)) ^ 2 = x := by
  show Real.rpow (Real.rpow _ _) _ = _
  rw [rpow_eq_pow, rpow_eq_pow, ← rpow_mul hx]
  norm_num

-- TODO: Move.
lemma Real.binomial_two (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + (2 * (x * y) + y ^ 2) := by
  simp only [rpow_two]; ring

-- TODO: Move.
lemma Real.exp_neg_eq_one_div (x : ℝ) : exp (-x) = 1 / exp x := by
  rw [exp_neg, inv_eq_one_div]

/-- Attempt to close the goal using the lemma specified with a combination of
`simp` and `rw`. -/
syntax "simp_or_rw" "[" Lean.Parser.Tactic.rwRule "]" : tactic

macro_rules
| `(tactic| simp_or_rw [$rule]) =>
  let symm := !rule.raw[0].isNone
  match rule.raw[1] with
  | `(term| $e:term) =>
    if symm then
      `(tactic| (first | simp only [←$e:term] | repeat' (rw [←$e:term])))
    else
      `(tactic| (first | simp only [$e:term] | repeat' (rw [$e:term])))

namespace CvxLean

/- Objective function rules. -/

register_objFun_rewrite_map "map_objFun_log"; "(prob (objFun ?a) ?cs)" => "(prob (objFun (log ?a)) ?cs)" :=
  map_objFun_log;

register_objFun_rewrite_map "map_objFun_sq"; "(prob (objFun ?a) ?cs)" => "(prob (objFun (pow ?a 2)) ?cs)" :=
  map_objFun_sq;


/- Equality rules. -/

register_rewrite_map "log_eq_log" ; "(eq ?a ?b)" => "(eq (log ?a) (log ?b))" :=
  rewrite [Real.log_eq_log (by arith) (by arith)];


/- Less than or equal rules. -/

register_rewrite_map "le_sub_iff_add_le" ; "(le ?a (sub ?b ?c))" => "(le (add ?a ?c) ?b)" :=
  rewrite [le_sub_iff_add_le];

register_rewrite_map "le_sub_iff_add_le-rev" ; "(le (add ?a ?c) ?b)" => "(le ?a (sub ?b ?c))" :=
  rewrite [←le_sub_iff_add_le];

register_rewrite_map "sub_le_iff_le_add"; "(le (sub ?a ?c) ?b)" => "(le ?a (add ?b ?c))" :=
  rewrite [sub_le_iff_le_add];

register_rewrite_map "sub_le_iff_le_add-rev"; "(le ?a (add ?b ?c))" => "(le (sub ?a ?c) ?b)" :=
  rewrite [←sub_le_iff_le_add];

register_rewrite_map "div_le_iff" ; "(le (div ?a ?b) ?c)" => "(le ?a (mul ?b ?c))" :=
  rewrite [div_le_iff (by arith)];

register_rewrite_map "div_le_iff-rev" ; "(le (div ?a ?b) ?c)" => "(le ?a (mul ?b ?c))" :=
  rewrite [←div_le_iff (by arith)];

register_rewrite_map "div_le_one-rev" ; "(le ?a ?b)" => "(le (div ?a ?b) 1)" :=
  rewrite [←div_le_one (by arith)];

register_rewrite_map "log_le_log" ; "(le (log ?a) (log ?b))" => "(le ?a ?b)" :=
  rewrite [Real.log_le_log (by arith) (by arith)];

register_rewrite_map "log_le_log-rev" ; "(le ?a ?b)" => "(le (log ?a) (log ?b))" :=
  rewrite [←Real.log_le_log (by arith) (by arith)];

register_rewrite_map "pow_two_le_pow_two"; "(le (pow ?a 2) (pow ?b 2))" => "(le ?a ?b)":=
  rewrite [Real.pow_two_le_pow_two (by arith) (by arith)];

register_rewrite_map "pow_two_le_pow_two-rev"; "(le ?a ?b)" => "(le (pow ?a 2) (pow ?b 2))" :=
  rewrite [←Real.pow_two_le_pow_two (by arith) (by arith)];


/- Field rules. -/

register_rewrite_map "neg_neg" ; "(neg (neg ?a))" => "?a" :=
  simp_or_rw [neg_neg (G := ℝ)];

register_rewrite_map "add_zero" ; "(add ?a 0)" => "?a" :=
  simp_or_rw [add_zero];

register_rewrite_map "add_comm" ; "(add ?a ?b)" => "(add ?b ?a)" :=
  simp_or_rw [add_comm];

register_rewrite_map "add_assoc" ; "(add (add ?a ?b) ?c)" => "(add ?a (add ?b ?c))" :=
  simp_or_rw [add_assoc];

register_rewrite_map "sub_self" ; "(sub ?a ?a)" => "0" :=
  simp_or_rw [sub_self];

register_rewrite_map "one_mul" ; "(mul 1 ?a)" => "?a" :=
  simp_or_rw [one_mul];

-- Exception, we cannot find the pattern otherwise.
register_rewrite_map "one_mul-rev" ; "?a" => "(mul 1 ?a)" :=
  norm_num;

register_rewrite_map "mul_zero" ; "(mul ?a 0)" => "0" :=
  simp_or_rw [mul_zero (M₀ := ℝ)];

register_rewrite_map "mul_comm" ; "(mul ?a ?b)" => "(mul ?b ?a)" :=
  simp_or_rw [mul_comm];

register_rewrite_map "mul_assoc" ; "(mul (mul ?a ?b) ?c)" => "(mul ?a (mul ?b ?c))" :=
  simp_or_rw [mul_assoc];

register_rewrite_map "sub_eq_add_neg"; "(sub ?a ?b)" => "(add ?a (neg ?b))" :=
  simp_or_rw [sub_eq_add_neg (G := ℝ)];

register_rewrite_map "sub_eq_add_neg-rev"; "(add ?a (neg ?b))" => "(sub ?a ?b)" :=
  simp_or_rw [←sub_eq_add_neg (G := ℝ)];

register_rewrite_map "add_sub" ; "(add ?a (sub ?b ?c))" => "(sub (add ?a ?b) ?c)" :=
  simp_or_rw [add_sub];

register_rewrite_map "add_sub-rev" ; "(add ?a (sub ?b ?c))" => "(sub (add ?a ?b) ?c)" :=
  simp_or_rw [←add_sub];

register_rewrite_map "add_mul" ; "(mul (add ?a ?b) ?c)" => "(add (mul ?a ?c) (mul ?b ?c))" :=
  simp_or_rw [add_mul];

register_rewrite_map "add_mul-rev" ; "(add (mul ?a ?c) (mul ?b ?c))" => "(mul (add ?a ?b) ?c)" :=
  simp_or_rw [←add_mul];

register_rewrite_map "mul_add" ; "(mul ?a (add ?b ?c))" => "(add (mul ?a ?b) (mul ?a ?c))" :=
  simp_or_rw [mul_add];

register_rewrite_map "mul_add-rev" ; "(add (mul ?a ?b) (mul ?a ?c))" => "(mul ?a (add ?b ?c))" :=
  simp_or_rw [←mul_add];

register_rewrite_map "mul_sub" ; "(mul ?a (sub ?b ?c))" => "(sub (mul ?a ?b) (mul ?a ?c))" :=
  simp_or_rw [←mul_sub];

register_rewrite_map "mul_sub-rev" ; "(sub (mul ?a ?b) (mul ?a ?c))" => "(mul ?a (sub ?b ?c))" :=
  simp_or_rw [←mul_sub];

register_rewrite_map "add_div" ; "(div (add ?a ?b) ?c)" => "(add (div ?a ?c) (div ?b ?c))" :=
  simp_or_rw [add_div];

register_rewrite_map "add_div-rev" ; "(add (div ?a ?c) (div ?b ?c))" => "(div (add ?a ?b) ?c)" :=
  simp_or_rw [←add_div];

register_rewrite_map "mul_div" ; "(mul ?a (div ?b ?c))" => "(div (mul ?a ?b) ?c)"  :=
  simp_or_rw [mul_div (G := ℝ)];

register_rewrite_map "mul_div-rev" ; "(div (mul ?a ?b) ?c)" => "(mul ?a (div ?b ?c))" :=
  simp_or_rw [←mul_div (G := ℝ)];

register_rewrite_map "div_self" ; "(div ?a ?a)" => "1" :=
  simp_or_rw [div_self (G₀ := ℝ) (by arith)];


/- Power and square root rules. -/

register_rewrite_map "one_pow"; "(pow 1 ?a)" => "1" :=
  simp_or_rw [Real.one_rpow];

register_rewrite_map "pow_one"; "(pow ?a 1)" => "?a" :=
  simp_or_rw [Real.rpow_one];

register_rewrite_map "pow_add"; "(pow ?a (add ?b ?c))" => "(mul (pow ?a ?b) (pow ?a ?c))" :=
  simp_or_rw [Real.rpow_add (by arith)];

register_rewrite_map "pow_add-rev"; "(mul (pow ?a ?b) (pow ?a ?c))" => "(pow ?a (add ?b ?c))" :=
  simp_or_rw [←Real.rpow_add (by arith)];

register_rewrite_map "mul_pow"; "(mul (pow ?a ?n) (pow ?b ?n))" => "(pow (mul ?a ?b) ?n)" :=
  simp_or_rw [Real.mul_rpow (by arith) (by arith)];

register_rewrite_map "mul_pow-rev"; "(mul (pow ?a ?n) (pow ?b ?n))" => "(pow (mul ?a ?b) ?n)" :=
  simp_or_rw [←Real.mul_rpow (by arith) (by arith)];

register_rewrite_map "pow_mul"; "(pow ?a (mul ?n ?m))" => "(pow (pow ?a ?n) ?m)" :=
  simp_or_rw [Real.rpow_mul (by arith)];

register_rewrite_map "pow_mul-rev"; "(pow (pow ?a ?n) ?m)" => "(pow ?a (mul ?n ?m))" :=
  simp_or_rw [←Real.rpow_mul (by arith)];

register_rewrite_map "div_pow"; "(pow (div ?a ?b) ?n)" => "(div (pow ?a ?n) (pow ?b ?n))" :=
  simp_or_rw [Real.div_rpow (by arith) (by arith)];

register_rewrite_map "div_pow-rev"; "(div (pow ?a ?n) (pow ?b ?n))" => "(pow (div ?a ?b) ?n)" :=
  simp_or_rw [←Real.div_rpow (by arith) (by arith)];

register_rewrite_map "pow_sub"; "(pow ?a (sub ?b ?c))" => "(div (pow ?a ?b) (pow ?a ?c))" :=
  simp_or_rw [Real.rpow_sub (by arith)];

register_rewrite_map "pow_sub-rev"; "(div (pow ?a ?b) (pow ?a ?c))" => "(pow ?a (sub ?b ?c))" :=
  simp_or_rw [←Real.rpow_sub (by arith)];

register_rewrite_map "div_pow_eq_mul_pow_neg" ; "(div ?a (pow ?b ?c))" => "(mul ?a (pow ?b (neg ?c)))" :=
  simp_or_rw [Real.div_pow_eq_mul_pow_neg (by arith)];

register_rewrite_map "div_pow_eq_mul_pow_neg-rev" ; "(div ?a (pow ?b ?c))" => "(mul ?a (pow ?b (neg ?c)))" :=
  simp_or_rw [←Real.div_pow_eq_mul_pow_neg (by arith)];

register_rewrite_map "one_div_eq_pow_neg_one"; "(div 1 ?a)" => "(pow ?a (neg 1))" :=
  simp_or_rw [Real.one_div_eq_pow_neg_one (by arith)];

register_rewrite_map "sqrt_eq_rpow" ; "(sqrt ?a)" => "(pow ?a 0.5)" :=
  simp_or_rw [Real.sqrt_eq_rpow];

register_rewrite_map "sqrt_eq_rpow-rev" ; "(pow ?a 0.5)" => "(sqrt ?a)" :=
  simp_or_rw [←Real.sqrt_eq_rpow];

register_rewrite_map "pow_two"; "(pow ?a 2)" => "(mul ?a ?a)" :=
  simp_or_rw [pow_two (M := ℝ)];

register_rewrite_map "pow_two-rev"; "(mul ?a ?a)" => "(pow ?a 2)" :=
  simp_or_rw [←pow_two (M := ℝ)];

register_rewrite_map "pow_half_two"; "(pow (pow ?a 0.5) 2)" => "?a" :=
  simp_or_rw [Real.pow_half_two (by arith)];

-- TODO(RFM): Technically ← but no pattern to match on otherwise.
register_rewrite_map "pow_half_two-rev"; "?a" => "(pow (pow ?a 0.5) 2)" :=
  simp_or_rw [Real.pow_half_two (by arith)];

register_rewrite_map "binomial_two"; "(pow (add ?a ?b) 2)" => "(add (pow ?a 2) (add (mul 2 (mul ?a ?b)) (pow ?b 2)))" :=
  simp_or_rw [Real.binomial_two];

/- Exponential and logarithm rules. -/

register_rewrite_map "exp_add" ; "(exp (add ?a ?b))" => "(mul (exp ?a) (exp ?b))" :=
  simp_or_rw [Real.exp_add];

register_rewrite_map "exp_add-rev" ; "(mul (exp ?a) (exp ?b))" => "(exp (add ?a ?b))" :=
  simp_or_rw [←Real.exp_add];

register_rewrite_map "exp_sub" ; "(exp (sub ?a ?b))" => "(div (exp ?a) (exp ?b))" :=
  simp_or_rw [Real.exp_sub];

register_rewrite_map "exp_sub-rev" ; "(div (exp ?a) (exp ?b))" => "(exp (sub ?a ?b))" :=
  simp_or_rw [←Real.exp_sub];

register_rewrite_map "exp_mul" ; "(exp (mul ?a ?b))" => "(pow (exp ?a) ?b)" :=
  simp_or_rw [Real.exp_mul];

register_rewrite_map "exp_mul-rev" ; "(pow (exp ?a) ?b)" => "(exp (mul ?a ?b))" :=
  simp_or_rw [←Real.exp_mul];

register_rewrite_map "exp_neg_eq_one_div"; "(exp (neg ?a))" => "(div 1 (exp ?a))" :=
  simp_or_rw [Real.exp_neg_eq_one_div];

register_rewrite_map "exp_neg_eq_one_div-rev" ; "(div 1 (exp ?a))" => "(exp (neg ?a))" :=
  simp_or_rw [←Real.exp_neg_eq_one_div];

register_rewrite_map "log_mul" ; "(log (mul ?a ?b))" => "(add (log ?a) (log ?b))" :=
  simp_or_rw [Real.log_mul (by arith) (by arith)];

register_rewrite_map "log_mul-rev"; "(add (log ?a) (log ?b))" => "(log (mul ?a ?b))" :=
  simp_or_rw [←Real.log_mul (by arith) (by arith)];

register_rewrite_map "log_div" ; "(log (div ?a ?b))" => "(sub (log ?a) (log ?b))" :=
  simp_or_rw [Real.log_div (by arith) (by arith)];

register_rewrite_map "log_div-rev"; "(sub (log ?a) (log ?b))" => "(log (div ?a ?b))" :=
  simp_or_rw [←Real.log_div (by arith) (by arith)];

register_rewrite_map "exp_log" ; "(exp (log ?a))" => "?a" :=
  simp_or_rw [Real.exp_log (by arith)];

register_rewrite_map "log_exp" ; "(log (exp ?a))" => "?a" :=
  simp_or_rw [Real.log_exp];


/- Atom folding. -/

register_rewrite_map "xexp_fold"; "(mul ?a (exp ?a))" => "(xexp ?a)" :=
  rfl;

register_rewrite_map "xexp_unfold"; "(xexp ?a)" => "(mul ?a (exp ?a))" :=
  rfl;

register_rewrite_map "entr_fold"; "(neg (mul ?a (log ?a)))" => "(entr ?a)" :=
  rfl;

register_rewrite_map "entr_unfold"; "(entr ?a)" => "(neg (mul ?a (log ?a)))" :=
  rfl;

register_rewrite_map "qol_fold"; "(div (pow ?a 2) ?b)" => "(qol ?a ?b)" :=
  rfl;

register_rewrite_map "qol_unfold"; "(qol ?a ?b)" => "(div (pow ?a 2) ?b)" :=
  rfl;

register_rewrite_map "geo_fold"; "(sqrt (mul ?a ?b))" => "(geo ?a ?b)" :=
  rfl;

register_rewrite_map "geo_unfold"; "(geo ?a ?b)" => "(sqrt (mul ?a ?b))" :=
  rfl;

register_rewrite_map "norm2_fold"; "(sqrt (add (pow ?a 2) (pow ?b 2)))" => "(norm2 ?a ?b)" :=
  rfl;

register_rewrite_map "norm2_unfold"; "(norm2 ?a ?b)" => "(sqrt (add (pow ?a 2) (pow ?b 2)))" :=
  rfl;

end CvxLean
