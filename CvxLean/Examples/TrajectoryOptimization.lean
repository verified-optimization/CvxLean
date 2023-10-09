import CvxLean.Command.Reduction
import CvxLean.Command.Solve

open CvxLean Minimization
open Matrix Real

noncomputable section TrajectoryOptimization

open Matrix

def originalBezier (K V A : ℝ) (k v a : ℝ) :=
  optimization (x0 x1 x2 : ℝ) (T : ℝ) 
    minimize T 
    subject to 
      hT : 1 ≤ T 
      hk0 : K * x0 ≤ k 
      hk1 : K * x1 ≤ k
      hk2 : K * x2 ≤ k
      hv1 : 2 * V * (x1 - x0) ≤ T * v
      hv2 : 2 * V * (x2 - x1) ≤ T * v
      ha : 2 * A * (x2 - 2 * x1 + x0) ≤ T ^ 2 * a



def convexBezier (K V A : ℝ) (k v a : ℝ) :=
  optimization (x0 x1 x2 : ℝ) (T : ℝ) (y : ℝ) 
    minimize y - T 
    subject to 
      hT : 1 ≤ T 
      hk0 : K * x0 ≤ k 
      hk1 : K * x1 ≤ k
      hk2 : K * x2 ≤ k
      hv10 : 2 * V * (x1 - x0) ≤ T * v
      hv21 : 2 * V * (x2 - x1) ≤ T * v
      ha : 2 * A * (x2 - 2 * x1 + x0) ≤ y * a
      hy : T ^ 2 ≤ y
      h' : if v < 0 then T * v ≤ sqrt y * v else True 

      -- hh: if v < 0 then Tv <= sqrt(y)v (convex)
-- this does not quite work! because if v < 0, once again the issue, then this
-- is not convex. but we have equivalence here.
-- here's an idea: since y > 0, we might just do y |=> e^u, then there are 
-- isses with rearranging  as V could be negative.

-- (assert 
--     (forall ((y0 Real) (y1 Real) (y2 Real) (Tp Real) (yp Real)) 
--         (=>
--             (and 
--                 (<= 1 Tp)
--                 (and 
--                     (<= (* K y0) k)
--                     (and 
--                         (<= (* K y1) k)
--                         (and 
--                             (<= (* K y2) k)
--                             (and 
--                                 (<= (* (* 2 V) (- y1 y0)) (* Tp v))
--                                 (and 
--                                     (<= (* (* 2 V) (- y2 y1)) (* Tp v)) 
--                                     (and 
--                                         (<= (* (* 2 A) (- y2 (- (* 2 y1) y0))) (* Tp v))
--                                         (<= (* Tp Tp) yp))))))))
--             (<= (- y T) (- yp Tp))
--         )
--     )
-- )

lemma x (K V A : ℝ) (k v a : ℝ) (S : Solution (relaxedBezier K V A k v a)) :
  S.point.2.2.2.1 = S.point.2.2.2.2 ^ 2 := by {
    rcases S with ⟨⟨x0, x1, x2, T, y⟩, hfeas, hopt⟩ 
    rcases hfeas with ⟨hT, hk0, hk1, hk2, hv1, hv2, ha, hy⟩ 
    have : y ≤ T ^ 2 := by {
      -- apply x0, x1, x2, sqrt y, T on hopt.
      have := hopt ⟨⟨x0, x1, x2, sqrt y, y⟩, 
          ⟨sorry, hk0, hk1, hk2, hv1, hv2, ha, sorry⟩⟩ -- provable
      simp only [objFun, relaxedBezier] at this 
      sorry -- and we're in business
    }
    -- easy because we have T^2 <= y
    sorry
  }

-- (set-logic ALL)
-- (set-option :produce-models true)
-- (declare-fun x0 () Real)
-- (declare-fun x1 () Real)
-- (declare-fun x2 () Real)
-- (declare-fun T () Real)
-- (declare-fun y () Real)
-- (declare-fun V () Real)
-- (declare-fun v () Real)
-- (declare-fun K () Real)
-- (declare-fun k () Real)
-- (declare-fun A () Real)
-- (declare-fun a () Real)

-- (assert (<= 1 T))
-- (assert (<= (* K x0) k))
-- (assert (<= (* K x1) k))
-- (assert (<= (* K x2) k))
-- (assert (<= (* (* 2 V) (- x1 x0)) (* T v)))
-- (assert (<= (* (* 2 V) (- x2 x1)) (* T v)))
-- (assert (<= (* (* 2 A) (- x2 (- (* 2 x1) x0))) (* T v) ) )

-- (assert (<= (* T T) y))

-- (assert (<= 1 y))

-- (assert (< v 0))

-- (assert (or 
--     (< (* (sqrt y) v) (* 2 (* V (- x1 x0))))
--     (< (* (sqrt y) v) (* 2 (* V (- x2 x1))))
-- ))

-- (check-sat)
-- (get-model)

-- Thing is that this map is really not needed ?
def relaxationBezierTight (K V A : ℝ) (k v a : ℝ)  : 
  Solution (originalBezier K V A k v a) → Solution (relaxedBezier K V A k v a) := 
  fun ⟨⟨x0opt, x1opt, x2opt, Topt⟩, 
       ⟨hTopt, hk0opt, hk1opt, hk2opt, hv1opt, hv2opt, haopt⟩, hoptimality⟩ => {
    point := ⟨x0opt, x1opt, x2opt, Topt, Topt ^ 2⟩,
    feasibility := ⟨hTopt, hk0opt, hk1opt, hk2opt, by {
      dsimp
      sorry -- this is ok too
    }, hv2opt, haopt, le_refl _⟩,
    optimality := fun ⟨⟨x0, x1, x2, T, y⟩, ⟨hT, hk0, hk1, hk2, hv1, hv2, ha, hy⟩⟩ => by {
      simp at hT hk0 hk1 hk2 hv1 hv2 ha hy
      simp only [originalBezier, relaxedBezier, objFun, constraints] at hoptimality ⊢;
      have hToptnn := le_trans zero_le_one hTopt
      have hToptsub1nn := sub_nonneg_of_le hTopt
      have hTnn := le_trans zero_le_one hT
      have hT2nn := pow_nonneg hTnn 2
      have h1leT2 := pow_le_pow_of_le_left zero_le_one hT 2
      simp only [one_pow] at h1leT2
      have hynn := le_trans hT2nn hy
      have h1ley := le_trans h1leT2 hy
      have h1lesqrty := sqrt_le_sqrt h1ley 
      simp only [sqrt_one] at h1lesqrty
      have hTlesqrty := (le_sqrt hTnn hynn).2 hy
      have ha' : 2 * A * (x2 - 2 * x1 + x0) ≤ (sqrt y) ^ 2 * a := by 
        rw [rpow_two, sq_sqrt hynn]
        exact ha

      have hv : 
          2 * V * (x1 - x0) ≤ (sqrt y) * v 
        ∧ 2 * V * (x2 - x1) ≤ (sqrt y) * v := by {
          by_cases h : 0 ≤ v
          { -- This is trivial
            -- because 0 <= v and T <= sqrt y so it follows from hv1 and hv2 and
            -- transitivity
            sorry }
          { have h := le_of_not_le h
            by_contra hc
            simp only [not_and_or, not_le] at hc
            have hvT := mul_nonpos_of_nonneg_of_nonpos hTnn h
            have hv1' := le_trans hv1 hvT
            have hv2' := le_trans hv2 hvT
            simp [mul_sub] at hv1' hv2'
            rcases hc with (hc1 | hc2)
            { have := lt_of_lt_of_le hc1 hv1
              -- simp [mul_sub] at hv1 hv2
              have : 2 * V * x2 - 2 * V * x1 - 2 * V * x0 ≤ 2 * T * v := by 
                
                sorry
              
              sorry }
            { sorry } 
          }
      }
      have hToptlesqrty := 
        hoptimality ⟨
          ⟨x0, x1, x2, sqrt y⟩, 
          ⟨h1lesqrty, hk0, hk1, hk2, hv.1, hv.2, ha'⟩⟩
      simp at hToptlesqrty
      have hTopt2ley : Topt ^ 2 ≤ y := 
        rpow_two _ ▸ (le_sqrt hToptnn hynn).1 hToptlesqrty
      rcases (lt_trichotomy T Topt) with (hTltTopt | hTeqTopt | hToptltT)
      { exact sub_le_sub (rpow_two Topt ▸ hTopt2ley) (le_of_lt hTltTopt) }
      { rw [hTeqTopt] at hy ⊢
        simp [hy] }
      { have hToptleT := le_of_lt hToptltT
        have hT2subTleysubT : T ^ 2 - T ≤ y - T := 
          sub_le_sub (rpow_two _ ▸ hy) (le_refl _)
        have hTopt2subToptleT2subT : Topt ^ 2 - Topt ≤ T ^ 2 - T := by 
          have hToptsub1leTsub1 := sub_le_sub hToptleT (le_refl 1)
          have hintermediate : Topt * Topt - Topt * 1 ≤ T * T - T * 1 := by 
            rw [←mul_sub, ←mul_sub]
            apply mul_le_mul hToptleT hToptsub1leTsub1 hToptsub1nn hTnn
          rw [rpow_two, rpow_two, pow_two, pow_two]
          simp only [mul_one] at hintermediate
          exact hintermediate
        exact le_trans hTopt2subToptleT2subT hT2subTleysubT } 
    } 
  }

def originalBezier' (n d : ℕ) 
  (K : Matrix (Fin (d + 2)) (Fin n) ℝ) 
  (V : Matrix (Fin (d + 1)) (Fin n) ℝ)
  (A : Matrix (Fin d) (Fin n) ℝ)
  (k : Fin (d + 2) → ℝ)
  (v : Fin (d + 1) → ℝ)
  (a : Fin d → ℝ) :=
  optimization (x : Fin n → ℝ) (T : ℝ) 
    minimize T 
    subject to 
      hT : 1 ≤ T 
      hk : K.mulVec x ≤ k 
      hv : V.mulVec x ≤ T • v
      ha : A.mulVec x ≤ T ^ 2 • a

def convexBezier' (n d : ℕ)
  (K : Matrix (Fin (d + 2)) (Fin n) ℝ)
  (V : Matrix (Fin (d + 1)) (Fin n) ℝ)
  (A : Matrix (Fin d) (Fin n) ℝ)
  (k : Fin (d + 2) → ℝ)
  (v : Fin (d + 1) → ℝ)
  (a : Fin d → ℝ) :=
  optimization (x : Fin n → ℝ) (T : ℝ) (y : ℝ)
    minimize y - T
    subject to
      hT : 1 ≤ T
      hk : K.mulVec x ≤ k
      hv : V.mulVec x ≤ T • v
      ha : A.mulVec x ≤ y • a
      hy : T ^ 2 ≤ y
      hfix : ∀ i, v i < 0 → T * v i ≤ sqrt y * v i

end TrajectoryOptimization