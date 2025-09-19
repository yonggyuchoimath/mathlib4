import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.TensorProduct.Cobar

/-!
# Equalizer of the inclusions to pushout in `CommRingCat`

Given a map `f : R ⟶ S` in `CommRingCat`, we prove that the equalizer of the two maps
`pushout.inl : S ⟶ pushout f f` and `pushout.inr : S ⟶ pushout f f` is isomorphic to `R`
if `R ⟶ S` is a faithfully flat ring map.

Note that, under `CommRingCat.pushoutCoconeIsColimit`, the two maps `inl` and `inr` can be written
as `s ↦ s ⊗ₜ[R] 1` and `s ↦ 1 ⊗ₜ[R] s`, respectively.
-/

open CategoryTheory Limits TensorProduct

namespace CommRingCat

universe u

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/--
The explicit cocone of form
```
R ---------f---------> S
|                      |
f                  includeLeft
|                      |
v                      v
S ----includeRight-->S ⊗[R] S
```
for a map `f : R ⟶ S` in `CommRingCat`.
-/
def pushoutCoconeOfSelf : PushoutCocone f f :=
  @CommRingCat.pushoutCocone R S S _ _ _ f.hom.toAlgebra f.hom.toAlgebra

/--
The explicit cone of form
```
R ---------f---------> S
|                      |
f                  includeLeft
|                      |
v                      v
S ----includeRight-->S ⊗[R] S
```
for a map `f : R ⟶ S` in `CommRingCat`.
-/
def pushoutCoconeOfSelf.cone :
    PullbackCone (pushoutCoconeOfSelf f).inl (pushoutCoconeOfSelf f).inr :=
  CommSq.cone ⟨PushoutCocone.condition (pushoutCoconeOfSelf f)⟩

/--
The explicit fork of form
```
        S ---includeLeft---> S ⊗[R] S
R --f-->
        S ---includeRight--> S ⊗[R] S
```
for a map `f : R ⟶ S` in `CommRingCat`.
-/
def forkOfSelf : Fork (pushoutCoconeOfSelf f).inl (pushoutCoconeOfSelf f).inr := by
  algebraize [f.hom]
  apply Fork.ofι f
  apply CommRingCat.hom_ext
  apply RingHom.coe_inj
  ext
  exact Algebra.TensorProduct.tmul_one_eq_one_tmul _

namespace Equalizer

section toEqualizer

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

noncomputable def toEqualizer :
    R →+* (equalizerFork (pushoutCoconeOfSelf f).inl (pushoutCoconeOfSelf f).inr).pt := by
  algebraize [f.hom]
  exact Algebra.TensorProduct.toEqLocus R S

lemma toEqualizer.inj_of_inj (hf : Function.Injective f.hom) :
    Function.Injective (toEqualizer f) := by
  algebraize [f.hom]
  exact Algebra.TensorProduct.toEqLocus.inj R S hf

lemma toEqualizer.surj_of_exact_trunc_augmented_cobar
    (hf : @Algebra.TensorProduct.exact_trunc_augmented_cobar R S _ _ f.hom.toAlgebra) :
    Function.Surjective (toEqualizer f) := by
  algebraize [f.hom]
  exact Algebra.TensorProduct.toEqLocus.surj R S hf

lemma toEqualizer.bij_of_faithfullyFlat (hf : f.hom.FaithfullyFlat) :
    Function.Bijective (toEqualizer f) := by
  constructor
  · exact toEqualizer.inj_of_inj _ (RingHom.FaithfullyFlat.injective hf)
  · algebraize [f.hom]
    exact toEqualizer.surj_of_exact_trunc_augmented_cobar _
      (Algebra.TensorProduct.exact_trunc_augmented_cobar.of_faithfullyFlat R S)

end toEqualizer

section Fork

noncomputable def isLimit_forkOfSelf (hf : f.hom.FaithfullyFlat) : IsLimit (forkOfSelf f) := by
  refine (Fork.isLimitEquivOfIsos _
    (equalizerFork (pushoutCoconeOfSelf f).inl (pushoutCoconeOfSelf f).inr)
    (Iso.refl _) (Iso.refl _) ?_ (by simp) (by simp) ?_).symm ?_
  · exact (RingEquiv.ofBijective _ (toEqualizer.bij_of_faithfullyFlat _ hf)).toCommRingCatIso
  · rfl
  · exact CommRingCat.equalizerForkIsLimit _ _

noncomputable def isLimit_fork_pushout_of_faithfullyFlat (hf : f.hom.FaithfullyFlat) :
    IsLimit (Fork.ofι f pushout.condition) := by
  algebraize [f.hom]
  let : IsPushout _ _ _ _ :=
    ⟨⟨PushoutCocone.condition (pushoutCocone R S S)⟩, ⟨pushoutCoconeIsColimit R S S⟩⟩
  exact Fork.isLimitEquivOfIsos (forkOfSelf f) _
    (Iso.refl _) (IsPushout.isoPushout this) (Iso.refl _)
      (IsPushout.inl_isoPushout_hom this).symm (IsPushout.inr_isoPushout_hom this).symm
        rfl (isLimit_forkOfSelf f hf)

end Fork

end Equalizer

end CommRingCat
