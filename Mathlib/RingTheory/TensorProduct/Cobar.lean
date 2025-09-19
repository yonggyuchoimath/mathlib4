import Mathlib.Algebra.Exact
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.RingHom.FaithfullyFlat

open scoped TensorProduct

namespace Algebra.TensorProduct

section

variable {R S : Type*} [CommSemiring R] [Ring S] [Algebra R S]

variable (R S) in
def leftMinusRight : S →ₗ[R] TensorProduct R S S :=
  (includeLeft (R := R) (S := R) (A := S) (B := S)).toLinearMap -
    (includeRight (R := R) (A:= S) (B := S)).toLinearMap

@[simp]
lemma leftMinusRight_apply (s : S) : leftMinusRight R S s = s ⊗ₜ[R] 1 - 1 ⊗ₜ[R] s :=
  rfl

lemma leftMinusRight_zero_of_range {s : S} (hs : s ∈ Set.range ⇑(Algebra.linearMap R S)) :
    (leftMinusRight R S) s = 0 := by
  obtain ⟨_, hr⟩ := Set.mem_range.mp hs
  simp only [← hr, leftMinusRight, linearMap_apply, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
    AlgHom.commutes, sub_self]

lemma leftMinusRight_eq_distrib_comp_lTensor (S : Type*) [Ring S] [Algebra R S] (T : Type*)
    [CommRing T] [Algebra R T] : (leftMinusRight T (T ⊗[R] S)).restrictScalars R =
    (TensorProduct.AlgebraTensorModule.distrib R T S S).toLinearMap.comp
      ((leftMinusRight R S).lTensor T) := by
  ext t s
  simp only [TensorProduct.AlgebraTensorModule.curry_apply,  TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, leftMinusRight_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, LinearMap.lTensor_tmul, TensorProduct.tmul_sub]
  simp only [sub_eq_add_neg, ← TensorProduct.neg_tmul,
    LinearEquiv.map_add, TensorProduct.AlgebraTensorModule.distrib_tmap]
  simp only [TensorProduct.neg_tmul, TensorProduct.one_def]
  have : t ⊗ₜ[R] (1 : S) = (algebraMap T (T ⊗[R] S)) t * (1 ⊗ₜ[R] 1) := by
    simp only [algebraMap_apply, algebraMap_self, RingHom.id_apply, tmul_mul_tmul, mul_one]
  rw [this, ← smul_def, TensorProduct.smul_tmul]
  simp only [smul_def, TensorProduct.algebraMap_apply, algebraMap_self, RingHom.id_apply,
    tmul_mul_tmul, mul_one, one_mul]

variable (R S) in
def exact_trunc_augmented_cobar : Prop :=
  Function.Exact ⇑(Algebra.linearMap R S) ⇑(leftMinusRight R S)

lemma exact_trunc_augmented_cobar.of_section (g : AlgHom R S R) :
    exact_trunc_augmented_cobar R S := by
  intro s
  constructor
  · intro hs
    rw [leftMinusRight_apply] at hs
    use g s
    apply (TensorProduct.lid R S).symm.injective
    rw [lid_symm_apply, lid_symm_apply, linearMap_apply, ← mul_one ((algebraMap R S) (g s)),
      ← Algebra.smul_def, ← TensorProduct.smul_tmul, smul_eq_mul, mul_one, ← id_eq (1 : S),
      ← AlgHom.coe_id R S, ← map_tmul, sub_eq_zero.mp hs, map_tmul, map_one, AlgHom.coe_id, id_eq]
  · exact leftMinusRight_zero_of_range

section FaithfullyFlat

variable (R : Type*) [CommRing R]

lemma lTensor_eq_comp_rid (S : Type*) [Semiring S] [Algebra R S] (T : Type*)
    [CommSemiring T] [Algebra R T] : ((Algebra.linearMap R S).lTensor T) =
    ((Algebra.linearMap T (T ⊗[R] S)).restrictScalars R).comp
      (TensorProduct.rid R R T).toLinearMap := by
  ext
  simp

lemma exact_trunc_augmented_cobar.desc_faithfullyFlat (S : Type*) [Ring S] [Algebra R S]
    (T : Type*) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
    (h : exact_trunc_augmented_cobar T (TensorProduct R T S)) :
    exact_trunc_augmented_cobar R S := by
  refine Module.FaithfullyFlat.lTensor_reflects_exact R T _ _ <|
    AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
      ((Algebra.linearMap R S).lTensor T).toAddMonoidHom
      ((leftMinusRight R S).lTensor T).toAddMonoidHom
      (Algebra.linearMap T (T ⊗[R] S)).toAddMonoidHom
      (leftMinusRight T (T ⊗[R] S)).toAddMonoidHom
      (TensorProduct.rid R R T).toAddMonoidHom
      (AddMonoidHom.id (T ⊗[R] S))
      (TensorProduct.AlgebraTensorModule.distrib R T S S).toAddMonoidHom
      (by ext; simp [lTensor_eq_comp_rid]) ?_
      (TensorProduct.rid R R T).surjective Function.bijective_id
      ((TensorProduct.AlgebraTensorModule.distrib R T S S).injective)|>.mpr h
  have : (leftMinusRight T (T ⊗[R] S)).toAddMonoidHom =
      ((leftMinusRight T (T ⊗[R] S)).restrictScalars R).toAddMonoidHom :=
    rfl
  simp only [this, leftMinusRight_eq_distrib_comp_lTensor]
  ext
  simp

lemma exact_trunc_augmented_cobar.of_faithfullyFlat (S : Type*) [CommRing S] [Algebra R S]
    [hS : Module.FaithfullyFlat R S] : exact_trunc_augmented_cobar R S :=
  exact_trunc_augmented_cobar.desc_faithfullyFlat R S S
    (exact_trunc_augmented_cobar.of_section (Algebra.TensorProduct.lmul'' R (S := S)))

section FixedUniverse

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

lemma algebraMap_tmul_one_comm (r : R) :
    (algebraMap R S) r ⊗ₜ[R] 1 = 1 ⊗ₜ[R] (algebraMap R S) r := by
  rw [← mul_one ((algebraMap R S) r), ← Algebra.smul_def, ← TensorProduct.smul_tmul]

def toEqLocus : R →+* (CommRingCat.pushoutCocone R S S).inl.hom.eqLocus
    (CommRingCat.pushoutCocone R S S).inr.hom where
  toFun r := Subtype.mk (algebraMap R S r)
    (by simp [RingHom.eqLocus, algebraMap_tmul_one_comm R S r])
  map_zero' := by apply Subtype.ext; simp
  map_one' := by apply Subtype.ext; simp
  map_add' _ _ := by simp
  map_mul' _ _ := by simp

lemma toEqLocus.inj (h : Function.Injective (algebraMap R S)) :
    Function.Injective (toEqLocus R S) := by
  intro _ _ h'
  simp only [toEqLocus, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Subtype.mk.injEq] at h'
  exact h h'

lemma toEqLocus.surj (h : exact_trunc_augmented_cobar R S) :
    Function.Surjective (toEqLocus R S) := by
  intro s
  have s_mem : s.val ∈ Set.range ⇑(Algebra.linearMap R S) :=
    (h s.val).mp ((leftMinusRight_apply (R := R) s.val).symm ▸ sub_eq_zero.mpr s.property)
  use (Set.mem_range.mp s_mem).choose
  ext
  nth_rw 5 [← (Set.mem_range.mp s_mem).choose_spec]
  simp only [toEqLocus, linearMap_apply, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]

end FixedUniverse

end FaithfullyFlat

end

end Algebra.TensorProduct
