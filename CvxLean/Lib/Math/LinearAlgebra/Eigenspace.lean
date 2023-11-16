import Mathlib.LinearAlgebra.Eigenspace.Basic

universe u v w

namespace Module

namespace End

variable {K R : Type v} {V M : Type w}
  [CommRing R] [AddCommGroup M] [Module R M] [Field K] [AddCommGroup V] [Module K V]

lemma eigenspace_add {f g : End R M} {a b : R} :
  eigenspace f a ⊓ eigenspace g b ≤ eigenspace (f + g) (a + b) := by
  rintro x ⟨hf, hg⟩
  simp only [eigenspace, SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply,
    algebraMap_end_apply] at hf hg
  simp only [eigenspace, map_add, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.add_apply,
    algebraMap_end_apply]
  rw [←add_sub, add_comm (a • x), ←sub_sub, hg, add_sub, add_zero, hf]

lemma eigenspace_one : eigenspace (1 : End R M) 1 = ⊤ := by
  apply eq_top_iff.2
  intros x _
  simp only [mem_eigenspace_iff, LinearMap.one_apply, one_smul]

lemma has_eigenvector_add {f g : End R M} {a b : R} {x : M}
    (hf : HasEigenvector f a x) (hg : HasEigenvector g b x) :
  HasEigenvector (f + g) (a + b) x :=
⟨eigenspace_add ⟨hf.1, hg.1⟩, hf.2⟩

lemma has_eigenvector_one {x : M} (hx : x ≠ 0) : HasEigenvector (1 : End R M) 1 x :=
⟨by { rw [eigenspace_one]; apply Submodule.mem_top }, hx⟩

end End

end Module
