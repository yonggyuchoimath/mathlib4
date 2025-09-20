/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.CategoryTheory.EffectiveEpi.Types
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.AlgebraicGeometry.PullbackCarrier
-- import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.Category.Ring.EqualizerPushout

/-!
# The fpqc topology is subcanonical

In this file we show that the fqpc topology of a scheme is subcanonical. This implies that
all coarser topologies, e.g., the (pro)étale topology, are subcanonical.
-/

universe v u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

----- EXACT COPY FROM PIONE's AlgebraicGeometry.MorphismProperty.Flat.lean
lemma flat_and_surjective_SpecMap_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Flat (Spec.map f) ∧ Surjective (Spec.map f) ↔ f.hom.FaithfullyFlat := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective, surjective_iff]
  rfl

lemma epi_of_flat_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [hf : Flat f] [Surjective f] :
    Epi f := by
  constructor
  intro Z g g' hg
  apply Scheme.Hom.ext'
  apply LocallyRingedSpace.Hom.ext'
  fapply SheafedSpace.hom_stalk_ext
  · apply ((TopCat.epi_iff_surjective f.base).mpr Surjective.surj).left_cancellation g.base g'.base
    rw [← Scheme.comp_coeBase, hg, Scheme.comp_coeBase]
  · intro y
    obtain ⟨x, hx⟩ := ‹Surjective f›.surj y
    rw [← hx]
    algebraize [(f.stalkMap x).hom]
    letI : Module.FaithfullyFlat (Y.presheaf.stalk (f.base.hom x)) (X.presheaf.stalk x) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ ((f.stalkMap x).hom.toAlgebra) _
        _ (Flat.stalkMap f x) (f.toLRSHom.prop x)
    apply ConcreteCategory.mono_of_injective _ (RingHom.FaithfullyFlat.injective ‹_›)
      |>.right_cancellation _ _
    have : PresheafedSpace.Hom.stalkMap (LocallyRingedSpace.Hom.toShHom (Hom.toLRSHom g)) =
        Hom.stalkMap g := by
      unfold Hom.stalkMap LocallyRingedSpace.Hom.stalkMap
      simp only
    rw [this]
    have : PresheafedSpace.Hom.stalkMap (LocallyRingedSpace.Hom.toShHom (Hom.toLRSHom g')) =
        Hom.stalkMap g' := by
      unfold Scheme.Hom.stalkMap LocallyRingedSpace.Hom.stalkMap
      simp only
    rw [this]
    rw [← Scheme.stalkMap_comp f g x, Category.assoc, ← Scheme.stalkMap_comp f g' x]
    simp only [stalkMap_congr_hom (f ≫ g) (f ≫ g') hg x]

-- Using `continuous_of_flat` below requires `Exists.choice`, as I formulated it as a `Prop`
-- in order to use `isEmpty_or_nonempty W.carrier`.
-- If I try to define `continuous_of_flat` as a type `def g : _ ⟶ _` together with an extra prop
-- `lemma _ : f.base ≫ g = e.base` (which will remove the `Exists.choice` required to call
-- `continuous_of_flat`),
-- then either
-- 1. `def g : _ ⟶ _` needs `Decidable (Nonempty W)` and `Decidable (IsEmpty W)`, or
-- 2. I can define `def g : _ ⟶ _` only under the assumption `[Nonempty W]`,
-- which raises same `Decidable` problem when defining
-- `def isColimit_cofork_pullback_condition : IsColimit _` later.

-- Failed to discrad the line `change pullback.fst ... = pullback.snd ...` in the proof.

/-- For a quasi-compact surjective flat morphism `f : X ⟶ Y` of schemes,
if `e : X ⟶ W` is a morphism of schemes for which `f : X ⟶ Y` plays the role of a coequalizer,
then `e : X ⟶ W` factors through some continuous map `g`  from the underlying topological
space of `Y` to that of `W`. -/
lemma continuous_of_flat {X Y : Scheme.{u}} {f : X ⟶ Y} [hf : Flat f]
    [hq : QuasiCompact f] [hs : Surjective f] {W : Scheme} {e : X ⟶ W}
    (h : pullback.fst f f ≫ e = pullback.snd f f ≫ e) :
    ∃ (g : TopCat.of Y.carrier ⟶ TopCat.of W.carrier), f.base ≫ g = e.base := by
  cases isEmpty_or_nonempty W.carrier
  · have : IsEmpty ↥X := Function.isEmpty ⇑e.base
    have : IsEmpty ↥Y := @Function.Surjective.isEmpty _ _ ‹_› _ hs.surj
    exact ⟨TopCat.ofHom ⟨isEmptyElim, (by continuity)⟩, TopCat.ext fun x ↦ isEmptyElim x⟩
  · have : ∃ (g : ↥Y → ↥W), ⇑(forgetToTop.map e).hom = g ∘ ⇑f.base.hom := by
      refine ⟨_, types_comp _ _ ▸ Cofork.IsColimit.π_desc'
        (regularEpi_pullback_of_surjective hs.surj).isColimit _ ?_|>.symm⟩
      change pullback.fst (Scheme.forget.map f) (Scheme.forget.map f) ≫ Scheme.forget.map e =
        pullback.snd (Scheme.forget.map f) (Scheme.forget.map f) ≫ Scheme.forget.map e
      apply ((epi_iff_surjective _).mpr
        (Scheme.Pullback.forget_comparison_surjective _ _)).left_cancellation _ _
      simp only [← Category.assoc, pullbackComparison_comp_fst, pullbackComparison_comp_snd,
        ← Functor.map_comp, h]
    use TopCat.ofHom <| Topology.IsQuotientMap.lift (Flat.isQuotientMap_of_surjective f)
      (Scheme.forgetToTop.map e).hom ((Function.factorsThrough_iff _).mpr this)
    apply TopCat.hom_ext
    rw [TopCat.hom_comp _ _]
    exact Topology.IsQuotientMap.lift_comp (Flat.isQuotientMap_of_surjective f)
      (Scheme.forgetToTop.map e).hom ((Function.factorsThrough_iff _).mpr this)

section BasicOpenCover

--- This can be generalized to any schemes, using local sections in place of `r`. ---
/-- For any continuous maps `f : C(X.carrier, Y.carrier)` for schemes `X` and `Y`,
if `X` is affine, then every point `x` of `X` admits a basic open neighborhood. -/
def basicOpen_continuous_of_isAffine {X Y : Scheme.{u}} [IsAffine X]
    (f : TopCat.of ↑X ⟶ TopCat.of Y) (x : X) : ∃ (r : Γ(X, ⊤)),
    x ∈ X.basicOpen r ∧ X.basicOpen r ≤ ⇑f ⁻¹' (Y.local_affine (f x)).choose.obj.carrier := by
  let temp := TopologicalSpace.Opens.isBasis_iff_nbhd.mp (isBasis_basicOpen X)
    (by simpa using (Y.local_affine (f x)).choose.property :
    x ∈ (TopologicalSpace.Opens.mk _ ((Y.local_affine (f x)).choose.obj.isOpen.preimage
      f.hom.continuous)))
  exact ⟨temp.choose_spec.left.choose,
    ⟨by rw [temp.choose_spec.left.choose_spec]; exact temp.choose_spec.right.left,
      by rw [temp.choose_spec.left.choose_spec]; exact temp.choose_spec.right.right⟩⟩

end BasicOpenCover

section
/-
In this section, we prove a relevant lifting to scheme morphism map needed for a proof of
effectivie epiness of flat qc covering of affine schemes.

We are given
1. a flat ring homomorphism `f : R ⟶ S` in `CommRingCat` such that
  `Spec.map f : Spec S ⟶ Spec R` is surjective, and
2. any scheme `U` with a morphism of schemes `e : Spec S ⟶ U` such that
```
pb (Spec f) (Spec.f) --- fst --> Spec S
          |                        |
         snd                       e
          ∨                        ∨
       Spec S------------ e -----> U
```
commutes.
-/
variable {R S : CommRingCat.{u}} {f : R ⟶ S}
variable [Flat (Spec.map f)] [Surjective (Spec.map f)]
variable {U : Scheme.{u}} {e : Spec S ⟶ U}
  (h : pullback.fst (Spec.map f) (Spec.map f) ≫ e = pullback.snd (Spec.map f) (Spec.map f) ≫ e)

/- For any point `p : (Spec R).carrier`, we will construct a commutative diagram of schemes
(except that `g` is going to be only a *continuous* map in the beginning steps)
```
      P  --- ιₛ ---> Spec S
    / |                 |  \
   /  f'         Spec.map f \
  /   ∨                 ∨    \
e'    W  --- ιᵣ ---> Spec R   e
  \   |                 |    /
   \  g'              g_pre /
    ↘ ∨                 ∨  ↙
      V  ---- ιᵤ -----> U
```
where
1. `g_pre : TopCat.of (Spec R).carrier ⟶ TopCat.of U.carrier` is the unique *continuous* map
  such that `(Spec.map f).base ≫ g_pre = e.base`,
2. `V` is any affine open subscheme of `U` containing `g_pre p : U`,
3. `W` denotes the basic open subscheme for some `r : Γ(Spec R, ⊤) (≅ R)` with `g_pre '' W ⊆ V`,
4. `ιᵣ : W ⟶ Spec R` denotes the open immersion for `W`,
5. `P` denotes the pullback of `ιᵣ : W ⟶ Spec R` and `(Spec.map f) : Spec S ⟶ Spec R`,
6. `f' : P ⟶ W` and `ιₛ : P ⟶ Spec S` denote the corresponding `pullback.fst` and `pullback.snd`,
  respectively, so that the top square is a pullback,
7. `e' : P ⟶ V` denotes the restriction of the morphism `ιₛ ≫ e : P ⟶ U` of schemes,
8. `g' : W ⟶ V` denotes the unique morphism of schemes such that `f' ≫ g' = e'` and
9. `ιᵤ : V ⟶ U` denotes the open immersion for `V`.
-/

local notation "g_pre" => Exists.choose (continuous_of_flat h)

variable (p : Spec R)

private noncomputable def ιᵤ := Scheme.Opens.ι
  (ObjectProperty.FullSubcategory.obj (Exists.choose (U.local_affine (g_pre p))))

private noncomputable def r := Exists.choose (basicOpen_continuous_of_isAffine g_pre p)

private noncomputable def ιᵣ := Scheme.Opens.ι (Scheme.basicOpen (Spec R) (r h p))

private noncomputable def ιₛ := pullback.snd (ιᵣ h p) (Spec.map f)

private noncomputable def f' := pullback.fst (ιᵣ h p) (Spec.map f)

private instance : Surjective (f' h p) := by
  rw [f']
  infer_instance

private instance (p : Spec R) : IsOpenImmersion (ιᵤ h p) := by
  rw [ιᵤ]
  infer_instance

private lemma lifting_e' : Set.range ⇑(ιₛ h p ≫ e).base.hom ⊆ Set.range ⇑(ιᵤ h p).base.hom := by
  nth_rw 1 [comp_base (ιₛ h p) e, (continuous_of_flat h).choose_spec.symm, ← Category.assoc,
    ← comp_base, ιₛ, ← pullback.condition, comp_base, ← f', Category.assoc]
  simp only [TopCat.hom_comp, TopCat.hom_comp, ContinuousMap.coe_comp, ContinuousMap.coe_comp,
    Surjective.surj.range_comp, Set.range_comp]
  change ⇑(continuous_of_flat h).choose.hom '' ((Spec R).basicOpen (r h p)).ι.opensRange.carrier ⊆
    (Opens.ι (U.local_affine (g_pre p)).choose.obj).opensRange.carrier
  simp only [Opens.opensRange_ι]
  exact Set.image_subset_iff.mpr (basicOpen_continuous_of_isAffine g_pre p).choose_spec.right

private noncomputable def e' (p : Spec R) :
    pullback (ιᵣ h p) (Spec.map f) ⟶ Opens.toScheme (U.local_affine (g_pre p)).choose.obj :=
  IsOpenImmersion.lift (ιᵤ h p) ((ιₛ h p) ≫ e) (lifting_e' h p)

private lemma snd_ιₛ_map_eq_fst_ιₛ_map : (pullback.snd (f' h p) (f' h p) ≫ (ιₛ h p)) ≫ Spec.map f =
    (pullback.fst (f' h p) (f' h p) ≫ (ιₛ h p)) ≫ (Spec.map f) := by
  simp only [Category.assoc, f', ιₛ, ← pullback.condition]
  simp only [← Category.assoc, ← pullback.condition]

private lemma pushoutComparison_inl_eq_inr :
    Γ.map (e' h p).op ≫ pushout.inl (Γ.map (f' h p).op) (Γ.map (f' h p).op) ≫
      pushoutComparison Γ (f' h p).op (f' h p).op =
    Γ.map (e' h p).op ≫ pushout.inr (Γ.map (f' h p).op) (Γ.map (f' h p).op) ≫
      pushoutComparison Γ (f' h p).op (f' h p).op := by
  simp only [inl_comp_pushoutComparison, inr_comp_pushoutComparison, ← Functor.map_comp]
  apply congr_arg Γ.map
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, Quiver.Hom.unop_op, ← pullbackIsoUnopPushout_inv_fst,
    ← pullbackIsoUnopPushout_inv_snd, Category.assoc]
  apply congr_arg ((pullbackIsoUnopPushout (f' h p) (f' h p)).inv ≫ ·)
  apply (cancel_mono (ιᵤ h p)).mp
  simp only [Category.assoc, e', IsOpenImmersion.lift_fac]
  rw [← Category.assoc, ← Category.assoc, ← pullback.lift_fst _ _ (snd_ιₛ_map_eq_fst_ιₛ_map h p)]
  nth_rw 1 [← pullback.lift_snd _ _ (snd_ιₛ_map_eq_fst_ιₛ_map h p)]
  exact congr_arg (_ ≫ ·) h.symm

private instance appTopfaithfullyFlat : RingHom.FaithfullyFlat (Γ.map (f' h p).op).hom := by
  rw [Γ_map_op]
  apply (flat_and_surjective_SpecMap_iff _).mp
  have : (asIso (pullback (ιᵣ h p) (Spec.map f)).toSpecΓ).inv ≫ f' h p ≫
    ((Spec R).basicOpen (r h p)).toScheme.toSpecΓ = Spec.map (Hom.appTop (f' h p)) := by
    apply (Iso.inv_comp_eq (asIso (pullback (ιᵣ h p) (Spec.map f)).toSpecΓ)).mpr
    simp only [Scheme.toSpecΓ_naturality (f' h p), asIso_hom]
  rw [← this, f']
  exact ⟨inferInstance, inferInstance⟩

private noncomputable def Γg' : Γ(Opens.toScheme (U.local_affine (g_pre p)).choose.obj, ⊤) ⟶
    Γ(((Spec R).basicOpen (r h p)).toScheme, ⊤) := by
  apply Fork.IsLimit.lift (CommRingCat.Equalizer.isLimit_fork_pushout_of_faithfullyFlat
    (Γ.map ((f' h p)).op) (appTopfaithfullyFlat h p)) (Γ.map ((e' h p)).op)
  exact (Pullback.pushoutComparison_Γ_of_isAffine (f' h p) (f' h p)).mono_of_iso.right_cancellation
    _ _ (pushoutComparison_inl_eq_inr h p)

private noncomputable def g' :
    ((Spec R).basicOpen (r h p)).toScheme ⟶ Opens.toScheme (U.local_affine (g_pre p)).choose.obj :=
  (((Spec R).basicOpen (r h p)).toScheme).isoSpec.hom ≫
    (Spec.map (Γg' h p)) ≫
      (Opens.toScheme (U.local_affine (g_pre p)).choose.obj).isoSpec.inv

private lemma g'_comp : f' h p ≫ g' h p = e' h p := by
  apply ext_of_isAffine
  have : (e' h p).appTop = Γg' h p ≫ (f' h p).appTop :=
    (Fork.IsLimit.lift_ι' (CommRingCat.Equalizer.isLimit_fork_pushout_of_faithfullyFlat
      (Γ.map (f' h p).op) (appTopfaithfullyFlat h p)) (Γ.map (e' h p).op) _).symm
  rw [comp_appTop, this]
  apply congr_arg (· ≫ _)
  simp only [g', comp_appTop, ← IsIso.Iso.inv_hom, inv_appTop, Category.assoc]
  apply (Iso.inv_comp_eq (asIso _)).mpr
  simp only [asIso_hom, Scheme.isoSpec_hom, toSpecΓ_appTop, ΓSpecIso_naturality]

private lemma snd_e_eq_f'_g'_ιᵤ : ιₛ h p ≫ e = f' h p ≫ g' h p ≫ ιᵤ h p := by
  rw [← Category.assoc, g'_comp]
  exact (IsOpenImmersion.lift_fac (ιᵤ h p) (ιₛ h p ≫ e) (lifting_e' h p)).symm


/- Now I have another point, and need to compare them. -/
/- !!! WRITE !!! -/
variable (q : Spec R)

/- Can I avoid this lemma? For that, I'd need a sort of compatibility, e.g., of
(isPullbackOuterSquare h p q).isoPullback.inv ≫ pullback.fst _ _ ≫ pullback.snd _ _
and
(SOME_OTHER_SQUARE).isoPullback.inv ≫ pullback.snd _ _ ≫ pullback.fst _ _
This particular one seems to require another IsPullback.paste_horiz, so maybe keep it for now. -/
private lemma pullback_lift_inv : pullback.lift
      (pullback.fst (f' h p ≫ ιᵣ h p) (f' h q ≫ ιᵣ h q) ≫ f' h p)
      (pullback.snd (f' h p ≫ ιᵣ h p) (f' h q ≫ ιᵣ h q) ≫ f' h q)
      (by simp [pullback.condition]) =
    (IsPullback.paste_horiz (IsPullback.of_hasPullback _ _) (IsPullback.paste_vert
      (IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback _ _))).isoPullback.inv ≫
    pullback.fst (pullback.snd _ _ ≫ pullback.snd _ _) _ ≫ pullback.snd _ _ := by
  refine (@cancel_mono _ _ _ _ _ (pullback.fst (ιᵣ h p) (ιᵣ h q)) ?_).mp ?_
  · simp only [ιᵣ]
    infer_instance
  · simp only [pullback.lift_fst, Category.assoc, ← pullback.condition]
    nth_rw 1 [← Category.assoc]
    rw [Category.assoc]
    nth_rw 2 [← Category.assoc]
    nth_rw 1 [← Category.assoc]
    rw [IsPullback.isoPullback_inv_fst _]

private lemma g'_pullback_condition : pullback.fst (ιᵣ h p) (ιᵣ h q) ≫ g' h p ≫ ιᵤ h p =
    pullback.snd (ιᵣ h p) (ιᵣ h q) ≫ g' h q ≫ ιᵤ h q := by
  apply (@cancel_epi _ _ _ _ _ (pullback.lift (f := ιᵣ h p) (g := ιᵣ h q)
    (pullback.fst (f' h p ≫ ιᵣ h p) (f' h q ≫ ιᵣ h q) ≫ f' h p)
    (pullback.snd (f' h p ≫ ιᵣ h p) (f' h q ≫ ιᵣ h q) ≫ f' h q)
    (by simp [pullback.condition])) ?_).mp ?_
  · rw [pullback_lift_inv h p q]
    simp only [f', ιᵣ, epi_of_flat_surjective]
  · simp only [← Category.assoc, pullback.lift_fst, pullback.lift_snd]
    simp only [Category.assoc]
    rw [← Category.assoc (f' h p) (g' h p) (ιᵤ h p), ← Category.assoc (f' h q) (g' h q) (ιᵤ h q)]
    simp only [g'_comp, e', IsOpenImmersion.lift_fac, ← Category.assoc]
    rw [← pullback.lift_fst (f := (Spec.map f)) (g := (Spec.map f))
      (pullback.fst (f' h p ≫ ιᵣ h p) (f' h q ≫ ιᵣ h q) ≫ ιₛ h p)
      (pullback.snd (f' h p ≫ ιᵣ h p) (f' h q ≫ ιᵣ h q) ≫ ιₛ h q)
      (by simp [ιₛ, f', ← pullback.condition])]
    nth_rw 2 [← pullback.lift_snd (f := (Spec.map f)) (g := (Spec.map f))
      (pullback.fst (f' h p ≫ ιᵣ h p) (f' h q ≫ ιᵣ h q) ≫ ιₛ h p)
      (pullback.snd (f' h p ≫ ιᵣ h p) (f' h q ≫ ιᵣ h q) ≫ ιₛ h q)
      (by simp [ιₛ, f', ← pullback.condition])]
    exact congr_arg (_ ≫ ·) h

end

section LiftToSchemeMap

/- !!! WRITE !!! -/

variable {R S : CommRingCat.{u}} {f : R ⟶ S}
variable [Flat (Spec.map f)] [Surjective (Spec.map f)]
variable {U : Scheme.{u}} {e : Spec S ⟶ U}
  (h : pullback.fst (Spec.map f) (Spec.map f) ≫ e = pullback.snd (Spec.map f) (Spec.map f) ≫ e)

private noncomputable def coverR : (Spec R).OpenCover where
  J := (Spec R).carrier
  obj p := ((Spec R).basicOpen
    (basicOpen_continuous_of_isAffine (continuous_of_flat h).choose p).choose).toScheme
  map p := ((Spec R).basicOpen
    (basicOpen_continuous_of_isAffine (continuous_of_flat h).choose p).choose).ι
  f p := p
  covers p := by
    rw [Opens.range_ι ((Spec R).basicOpen _)]
    exact (basicOpen_continuous_of_isAffine _ _).choose_spec.left
  map_prop := by infer_instance

private noncomputable def g : Spec R ⟶ U :=
  (coverR h).glueMorphisms
    (fun p => g' h p ≫ Opens.ι (U.local_affine ((continuous_of_flat h).choose p)).choose.obj)
    (fun x y => g'_pullback_condition h x y)

private lemma g_comp : Spec.map f ≫ g h = e := by
  apply Cover.hom_ext (Cover.pullbackCover' (coverR h) (Spec.map f))
  intro p
  simp only [Cover.pullbackCover', coverR]
  change _ = ιₛ h p ≫ e
  rw [snd_e_eq_f'_g'_ιᵤ h p, ← Category.assoc, ← pullback.condition, Category.assoc]
  exact congr_arg (_ ≫ ·) (Cover.ι_glueMorphisms (coverR h) (fun p => _) (fun x y => _) p)

private lemma g_unique (t : Spec R ⟶ U) (ht : Spec.map f ≫ t = e) : t = g h := by
  apply Cover.hom_ext (coverR h)
  intro p
  have : Epi (pullback.snd (Spec.map f) ((coverR h).map p)) :=
    epi_of_flat_surjective _
  apply (cancel_epi (pullback.snd (Spec.map f) ((coverR h).map p))).mp
  rw [← Category.assoc, ← Category.assoc, ← pullback.condition, Category.assoc, Category.assoc,
    ht, g_comp h]

end LiftToSchemeMap

noncomputable def isColimit_cofork_pullback_condition {R S : CommRingCat.{u}}
    (f : R ⟶ S) (hf : f.hom.Flat) (hs : Surjective (Spec.map f)) :
    IsColimit (Cofork.ofπ (Spec.map f) pullback.condition) := by
  apply Cofork.IsColimit.mk' _
  intro s
  have : Flat (Spec.map f) := HasRingHomProperty.Spec_iff.mpr hf
  use g s.condition
  constructor
  · simp only [Cofork.π_ofπ, g_comp s.condition]
  · intro t ht
    exact g_unique s.condition t ht

noncomputable def regularEpi_of_flat {R S : CommRingCat.{u}} (f : R ⟶ S) (hf : f.hom.Flat)
    (hs : Surjective (Spec.map f)) : RegularEpi (Spec.map f) where
  W := pullback (Spec.map f) (Spec.map f)
  left := pullback.fst (Spec.map f) (Spec.map f)
  right := pullback.snd (Spec.map f) (Spec.map f)
  w := pullback.condition
  isColimit := isColimit_cofork_pullback_condition f hf hs

noncomputable def effectiveEpiStruct_of_flat {R S : CommRingCat.{u}} (f : R ⟶ S) (hf : f.hom.Flat)
    (hs : Surjective (Spec.map f)) : EffectiveEpiStruct (Spec.map f) :=
  @effectiveEpiStructOfRegularEpi _ _ _ _ _ (regularEpi_of_flat f hf hs)

lemma effectiveEpi_of_flat {R S : CommRingCat.{u}} (f : R ⟶ S) (hf : f.hom.Flat)
    (hs : Surjective (Spec.map f)) : EffectiveEpi (Spec.map f) :=
  ⟨⟨effectiveEpiStruct_of_flat f hf hs⟩⟩

end AlgebraicGeometry
