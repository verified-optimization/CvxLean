import CvxLean.Tactic.PreDCP.RewriteMapCmd 
import CvxLean.Tactic.PreDCP.Basic

-- TODO(RFM): Move.
lemma Real.log_eq_log {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : Real.log x = Real.log y ↔ x = y :=
  ⟨fun h => by { 
    have hxmem := Set.mem_Ioi.2 hx
    have hymem := Set.mem_Ioi.2 hy
    have heq : Set.restrict (Set.Ioi 0) log ⟨x, hxmem⟩ = 
      Set.restrict (Set.Ioi 0) log ⟨y, hymem⟩ := by 
      simp [h]
    have h := Real.log_injOn_pos.injective heq
    simp [Subtype.eq] at h
    exact h
  }, fun h => by rw [h]⟩

-- TODO(RFM): Move.
lemma Real.div_pow_eq_mul_pow_neg {a b c : ℝ} (hb : 0 ≤ b) : a / (b ^ c) = a * b ^ (-c) := by
  rw [div_eq_mul_inv, ←rpow_neg hb]

-- TODO(RFM): Move.
lemma Real.exp_neg_eq_one_div (x : ℝ) : exp (-x) = 1 / exp x := by
  rw [exp_neg, inv_eq_one_div]


namespace CvxLean

/- Equality rules. -/

register_rewrite_map "log_eq_log" ; "(eq ?a ?b)" => "(eq (log ?a) (log ?b))" :=
  rw [Real.log_eq_log (by positivity) (by positivity)]


/- Less than or equal rules. -/

register_rewrite_map "le_sub_iff_add_le" ; "(le ?a (sub ?b ?c))" => "(le (add ?a ?c) ?b)" := 
  rw [le_sub_iff_add_le]

register_rewrite_map "div_le_iff" ; "(le (div ?a ?b) ?c)" => "(le ?a (mul ?b ?c))" := 
  rw [div_le_iff (by positivity)]

register_rewrite_map "div_le_iff-rev" ; "(le (div ?a ?b) ?c)" => "(le ?a (mul ?b ?c))" := 
  rw [←div_le_iff (by positivity)]

register_rewrite_map "div_le_one-rev" ; "(le ?a ?b)" => "(le (div ?a ?b) 1)" :=
  rw [←div_le_one (by positivity)]

register_rewrite_map "log_le_log" ; "(le (log ?a) (log ?b))" <=> "(le ?a ?b)" :=
  rw [Real.log_le_log (by positivity) (by positivity)]


/- Field rules. -/

register_rewrite_map "one_mul" ; "(mul 1 ?a)" <=> "?a" :=
  norm_num

register_rewrite_map "add_comm" ; "(add ?a ?b)" => "(add ?b ?a)" :=
  simp only [add_comm]

register_rewrite_map "add_assoc" ; "(add (add ?a ?b) ?c)" => "(add ?a (add ?b ?c))" :=
  simp only [add_assoc]

register_rewrite_map "mul_comm" ; "(mul ?a ?b)" => "(mul ?b ?a)" :=
  simp only [mul_comm]

register_rewrite_map "mul_assoc" ; "(mul (mul ?a ?b) ?c)" => "(mul ?a (mul ?b ?c))" :=
  simp only [mul_assoc]

register_rewrite_map "add_sub" ; "(add ?a (sub ?b ?c))" => "(sub (add ?a ?b) ?c)" := 
  simp only [add_sub]

register_rewrite_map "add_mul" ; "(mul (add ?a ?b) ?c)" => "(add (mul ?a ?c) (mul ?b ?c))" :=
  simp only [add_mul]

register_rewrite_map "add_mul-rev" ; "(add (mul ?a ?c) (mul ?b ?c))" => "(mul (add ?a ?b) ?c)" :=
  simp only [add_mul]

register_rewrite_map "mul_add" ; "(mul ?a (add ?b ?c))" => "(add (mul ?a ?b) (mul ?a ?c))" :=
  simp only [mul_add]

register_rewrite_map "mul_sub-rev" ; "(sub (mul ?a ?b) (mul ?a ?c))" => "(mul ?a (sub ?b ?c))" :=
  simp only [←mul_sub]

register_rewrite_map "add_div" ; "(div (add ?a ?b) ?c)" => "(add (div ?a ?c) (div ?b ?c))" :=
  simp only [add_div]

register_rewrite_map "mul_div" ; "(mul ?a (div ?b ?c))" => "(div (mul ?a ?b) ?c)"  :=
  simp only [mul_div]

register_rewrite_map "mul_div-rev" ; "(div (mul ?a ?b) ?c)" => "(mul ?a (div ?b ?c))" :=
  simp only [←mul_div]

register_rewrite_map "div_self" ; "(div ?a ?a)" => "1" :=
  simp only [@div_self ℝ _ _ (by positivity)]


/- Power and square root rules. -/

-- NOTE(RFM): This was conv in (_ / (_ ^  _)).
register_rewrite_map "div_pow_eq_mul_pow_neg" ; "(div ?a (pow ?b ?c))" => "(mul ?a (pow ?b (neg ?c)))" :=
  simp only [Real.div_pow_eq_mul_pow_neg (by positivity)]

register_rewrite_map "sqrt_eq_rpow" ; "(sqrt ?a)" => "(pow ?a 0.5)" :=
  simp only [Real.sqrt_eq_rpow]


/- Exponential and logarithm rules. -/

register_rewrite_map "exp_add" ; "(exp (add ?a ?b))" => "(mul (exp ?a) (exp ?b))" :=
  simp only [Real.exp_add]

register_rewrite_map "exp_add-rev" ; "(mul (exp ?a) (exp ?b))" => "(exp (add ?a ?b))" :=
  simp only [←Real.exp_add]

register_rewrite_map "exp_sub" ; "(exp (sub ?a ?b))" => "(div (exp ?a) (exp ?b))" :=
  simp only [Real.exp_sub]

register_rewrite_map "exp_sub-rev" ; "(div (exp ?a) (exp ?b))" => "(exp (sub ?a ?b))" :=
  simp only [←Real.exp_sub]

register_rewrite_map "exp_mul" ; "(exp (mul ?a ?b))" => "(pow (exp ?a) ?b)" :=
  simp only [Real.exp_mul]

register_rewrite_map "exp_mul-rev" ; "(pow (exp ?a) ?b)" => "(exp (mul ?a ?b))" :=
  simp only [←Real.exp_mul]

register_rewrite_map "exp_neg_eq_one_div-rev" ; "(div 1 (exp ?a))" => "(exp (neg ?a))" :=
  simp only [←Real.exp_neg_eq_one_div]

register_rewrite_map "log_mul" ; "(log (mul ?a ?b))" => "(add (log ?a) (log ?b))" :=
  rw [Real.log_mul (by positivity) (by positivity)]

register_rewrite_map "log_div" ; "(log (div ?a ?b))" => "(sub (log ?a) (log ?b))" :=
  simp only [Real.log_div (by positivity) (by positivity)]

register_rewrite_map "log_exp" ; "(log (exp ?a))" => "?a" :=
  simp only [Real.log_exp]

register_rewrite_map "exp_log" ; "(exp (log ?a))" => "?a" :=
  simp only [Real.exp_log (by positivity)]

end CvxLean
