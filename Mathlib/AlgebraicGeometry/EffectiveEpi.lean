/-
Copyright (c) 2025 Yong-Gyu Choi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yong-Gyu Choi
-/
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.PullbackCarrier
-- import Mathlib.Algebra.Category.Ring.EqualizerPushout
import Mathlib.Topology.Category.TopCat.EffectiveEpi
import Mathlib.CategoryTheory.EffectiveEpi.RegularEpi

/-!
# Effective epimorphisms in the category of schemes

We prove that are effective epimorphisms in the category of schemes.

## Main results

* `AlgebraicGeometry.Flat.descSpec` : Given a flat ring map `f : R ⟶ S` with surjective
  `Spec.map f : Spec S ⟶ Spec R` and a morphism `e : Spec S ⟶ U` of schemes which coequalizes
  the two projections `(Spec S) ×[Spec R] (Spec S) ⟶ Spec S`, this constructs the unique morphism
  `Spec R ⟶ U` of schemes through which `e` factors.

* `AlgebraicGeometry.Flat.pullbackCoforkIsColimit` : The cofork formed by the two projections
  `(Spec S) ×[Spec R] (Spec S) ⟶ Spec S` followed by `Spec S ⟶ Spec R` is a colimit when
  `f : R ⟶ S` is a flat ring map with surjective `Spec.map f`.

* `AlgebraicGeometry.Flat.effectiveEpi_of_flat_of_surjective` : Any surjective map
  `Spec.map f : Spec S ⟶ Spec R` with flat `f : R ⟶ S` is an effective epimorphism
  in the category of schemes.

## Reference

* https://stacks.math.columbia.edu/tag/023Q

-/

universe v u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Flat

lemma flat_and_surjective_iff_of_faithfullyFlat_of_isAffine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    Flat f ∧ Surjective f ↔ f.appTop.hom.FaithfullyFlat := by
  sorry

noncomputable def _root_.CommRingCat.Opposite.isColimitOfπPullbackOfFaithfullyFlat
    {R S : CommRingCat.{u}ᵒᵖ} (f : S ⟶ R) (hf : f.unop.hom.FaithfullyFlat) :
    IsColimit (Cofork.ofπ f pullback.condition) := by
  sorry

section AffineScheme

variable {X Y : AffineScheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f]

noncomputable def AffineScheme.regularEpiOfFlatOfSurjective : RegularEpi f where
  W := pullback f f
  left := pullback.fst f f
  right := pullback.snd f f
  w := pullback.condition
  isColimit := by
    apply isColimitOfReflects AffineScheme.equivCommRingCat.functor
    apply (isColimitMapCoconeCoforkEquiv _ _).symm ?_
    refine Cofork.isColimitOfIsos (Cofork.ofπ _ pullback.condition) ?_ _
      (PreservesPullback.iso _ f f).symm (.refl _) (.refl _) (by simp) (by simp) (by simp)
    apply CommRingCat.Opposite.isColimitOfπPullbackOfFaithfullyFlat _
    simp only [AffineScheme.equivCommRingCat, CategoryTheory.Equivalence.symm_functor,
      equivEssImageOfReflective_inverse, Functor.comp_map, ObjectProperty.ι_map, reflector,
      Reflective.L, Functor.rightOp_map_unop, Γ_map_op]
    exact (flat_and_surjective_iff_of_faithfullyFlat_of_isAffine f).mp ⟨‹_›, ‹_›⟩

lemma AffineScheme.effectiveEpiOfFlatOfSurjective : EffectiveEpi f :=
  let := AffineScheme.regularEpiOfFlatOfSurjective f
  ⟨⟨effectiveEpiStructOfRegularEpi f⟩⟩


-- noncomputable def CommRingCat.Opposite.isColimitOfπPullbackOfFaithfullyFlat (hf : f.unop.hom.FaithfullyFlat) :
--     IsColimit (Cofork.ofπ f pullback.condition) :=
--   Cofork.isColimitCoforkPushoutEquivIsColimitForkUnopPullback.symm
--     (Equalizer.isLimitForkPushoutSelfOfFaithfullyFlat _ hf)

-- /-- A regular epimorphism structure on a map `f : S ⟶ R` in `CommRingCatᵒᵖ` with
-- faithfully flat `f.unop : R.unop ⟶ S.unop`. -/
-- noncomputable def CommRingCat.Opposite.regularEpiOfFaithfullyFlat (hf : f.unop.hom.FaithfullyFlat) : RegularEpi f where
--   W := pullback f f
--   left := pullback.fst f f
--   right := pullback.snd f f
--   w := pullback.condition
--   isColimit := isColimitOfπPullbackOfFaithfullyFlat f hf

-- /-- Any map `f : S ⟶ R` in `CommRingCatᵒᵖ` with faithfully flat `f.unop : R.unop ⟶ S.unop` is
-- an effective epimorphism. -/
-- lemma effectiveEpi_of_faithfullyFlat (hf : f.unop.hom.FaithfullyFlat) : EffectiveEpi f := by
--   let := regularEpiOfFaithfullyFlat f hf
--   infer_instance

end AffineScheme

section Spec

/-
In this section, we prove a lifting result for morphisms from `Spec` to schemes that is needed to
establish that flat surjective morphisms between affine schemes are effective epimorphisms in the
category of schemes.

Given:
1. A flat ring homomorphism `f : R ⟶ S` in `CommRingCat` such that the induced morphism of schemes
  `Spec.map f : Spec S ⟶ Spec R` is surjective.
2. An arbitrary scheme `U` equipped with a morphism `e : Spec S ⟶ U` of schemes which coequalizes
  the two pullback projections of the self-pullback of `Spec.map f`, namely:
  `pullback.fst (Spec.map f) (Spec.map f) ≫ e = pullback.snd (Spec.map f) (Spec.map f) ≫ e`.

We construct a morphism `descSpec : Spec R ⟶ U` of schemes through which `e` factors.

**Step 1:** We define `desc : (Spec R).carrier ⟶ U.carrier` as the unique continuous map
satisfying `(Spec.map f).base ≫ desc = e.base`.

**Step 2:** For each point `p : (Spec R).carrier`, we construct the following commutative diagram:
```
      P  --- ιₛ ---> Spec S
    / |                 |  \
   /  f'         Spec.map f \
  /   ∨                 ∨    \
e'    W  --- ιᵣ ---> Spec R   e
  \   |                 |    /
   \ desc'            desc  /
    ↘ ∨                 ∨  ↙
      V  ---- ιᵤ -----> U
```
Here, `V` denotes an affine open containing `desc p`, `W` denotes a basic open in `Spec R` mapping
into `V`, and `P` denotes the pullback of `W` with `Spec S`. The morphisms in the diagram are:
- `ιᵤ`, `ιᵣ`, `ιₛ` : the natural open immersions
- `f'` : the pullback projection to `W`
- `e'` : the restriction of `ιₛ ≫ e` to `V`
- `desc'` : the unique morphism of schemes satisfying `f' ≫ desc' = e'`

**Step 3:** We show that the morphisms `desc'` for each `p` obtained in Step 2 glue together to
define a unique morphism `descSpec : Spec R ⟶ U` of schemes such that `Spec.map f ≫ descSpec = e`
(so `descSpec.base = desc`).
-/

/-- A preparation lemma for `base_factorization`. -/
private lemma base_factorization_type {X Y : Scheme.{u}} {f : X ⟶ Y} [Surjective f]
    {W : Scheme.{u}} {e : X ⟶ W} (h : pullback.fst f f ≫ e = pullback.snd f f ≫ e) :
    ∃ (g : ↥Y → ↥W), ⇑e.base.hom = g ∘ ⇑f.base.hom := by
  let : RegularEpi (Scheme.forget.map f) := by
    have := (isSplitEpi_iff_surjective (Scheme.forget.map f)).mpr ‹Surjective f›.surj
    exact regularEpiOfEffectiveEpi (Scheme.forget.map f)
  refine ⟨_, types_comp _ _ ▸ Cofork.IsColimit.π_desc' this.isColimit _ ?_|>.symm⟩
  change pullback.fst _ _ ≫ Scheme.forget.map e = pullback.snd _ _ ≫ Scheme.forget.map e
  apply ((epi_iff_surjective _).mpr
    (Scheme.pullbackComparison_forget_surjective _ _)).left_cancellation
  simp only [← Category.assoc, pullbackComparison_comp_fst, ← Functor.map_comp, h,
    pullbackComparison_comp_snd]

/-- For a flat surjective and quasi-compact morphism `f : X ⟶ Y` of schemes,
any morphism `e : X ⟶ W` of schemes satisfying `pullback.fst f f ≫ e = pullback.snd f f ≫ e`
factors through a unique *continuous map* on underlying topological spaces. -/
private lemma base_factorization {X Y : Scheme.{u}} {f : X ⟶ Y} [Flat f] [Surjective f]
    [QuasiCompact f] {W : Scheme.{u}} {e : X ⟶ W}
    (h : pullback.fst f f ≫ e = pullback.snd f f ≫ e) :
    ∃! (g : Y.carrier ⟶ W.carrier), f.base ≫ g = e.base := by
  have {Z : TopCat} (g₁ g₂ : Z ⟶ X.carrier) (hg : g₁ ≫ f.base = g₂ ≫ f.base) :
      g₁ ≫ e.base = g₂ ≫ e.base := by
    apply TopCat.hom_ext
    apply ContinuousMap.coe_injective
    simp only [TopCat.hom_comp, ContinuousMap.coe_comp]
    rw [(base_factorization_type h).choose_spec, Function.comp_assoc]
    congr 1
    exact congrArg (fun g ↦ g.toFun) ((TopCat.hom_comp _ _).trans (congrArg (fun g ↦ g.hom) hg))
  exact ⟨(TopCat.effectiveEpiStructOfQuotientMap _ (isQuotientMap_of_surjective f)).desc _ this,
    ⟨(TopCat.effectiveEpiStructOfQuotientMap _ (isQuotientMap_of_surjective f)).fac _ this,
      fun g' hg' ↦ (TopCat.effectiveEpiStructOfQuotientMap _ (isQuotientMap_of_surjective f)).uniq _
        this g' hg'⟩⟩

/-- A useful preparatory lemma when defining `ιᵣ`, `ιₛ` and `f'`. -/
private lemma exists_basicOpen_preimage_opens {X Y : Scheme.{u}} [IsAffine X]
    {f : X.carrier ⟶ Y.carrier} {x : X} {V : Y.Opens} (hx : f x ∈ V.carrier) :
    ∃ (r : Γ(X, ⊤)), x ∈ X.basicOpen r ∧ X.basicOpen r ≤ ⇑f ⁻¹' V.carrier :=
  have := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    (isBasis_basicOpen X) (V.mem_comap.mpr hx)).choose_spec
  ⟨this.left.choose,
    ⟨this.left.choose_spec.symm ▸ this.right.left, this.left.choose_spec.symm ▸ this.right.right⟩⟩

variable {R S : CommRingCat.{u}} {f : R ⟶ S}
variable [Flat (Spec.map f)] [Surjective (Spec.map f)]
variable {U : Scheme.{u}} {e : Spec S ⟶ U}
  (h : pullback.fst (Spec.map f) (Spec.map f) ≫ e = pullback.snd (Spec.map f) (Spec.map f) ≫ e)

/-- The unique continuous map satisfying `(Spec.map f).base ≫ desc = e.base`.-/
local notation "desc" => Exists.choose (Flat.base_factorization h)

variable {p : Spec R}

private noncomputable def ιᵤ (V : U.Opens) : V.toScheme ⟶ U := Scheme.Opens.ι V

private instance (V : U.Opens) : IsOpenImmersion (ιᵤ V) := by
  rw [ιᵤ]
  infer_instance

variable {V : U.Opens}

/-- An element in `Γ(Spec R, ⊤) (≅ R)` defining the basic open subset `W` in `Spec R`. -/
private noncomputable def r (hp : desc p ∈ V) :
    Γ(Spec R, ⊤).carrier :=
  (exists_basicOpen_preimage_opens hp).choose

private noncomputable def ιᵣ (hp : desc p ∈ V) :
    ((Spec R).basicOpen (r h hp)).toScheme ⟶ Spec R :=
  (Scheme.basicOpen (Spec R) (r h hp)).ι

private noncomputable def f' (hp : desc p ∈ V) :
    pullback (ιᵣ h hp) (Spec.map f) ⟶ ↑((Spec R).basicOpen (r h hp)) :=
  pullback.fst (ιᵣ h hp) (Spec.map f)

private noncomputable def ιₛ (hp : desc p ∈ V) :
    pullback (ιᵣ h hp) (Spec.map f) ⟶ Spec S :=
  pullback.snd (ιᵣ h hp) (Spec.map f)

/-- The underlying ring maps of `f'` is faithfully flat. -/
private lemma appTopfaithfullyFlat (hp : desc p ∈ V) : (Γ.map (f' h hp).op).hom.FaithfullyFlat := by
  apply (flat_and_surjective_iff_of_faithfullyFlat_of_isAffine _).mp
  simp only [f', Quiver.Hom.unop_op]
  exact ⟨inferInstance, inferInstance⟩

/-- In the outer square, the (set-theoretic) image of the composition of the top and right vertical
maps is contained in the (set-theoretic) image of the bottom map. -/
private lemma range_ιₛ_e_subset_ιᵤ (hp : desc p ∈ V) :
    Set.range ⇑(ιₛ h hp ≫ e).base.hom ⊆ Set.range ⇑(ιᵤ V).base.hom := by
  nth_rw 1 [Hom.comp_base (ιₛ h hp) e, (base_factorization h).choose_spec.left.symm,
    ← Category.assoc, ← Hom.comp_base, ιₛ, ← pullback.condition, Hom.comp_base, ← f',
    Category.assoc]
  have : Surjective (f' h hp) := by rw [f']; infer_instance
  simp only [TopCat.hom_comp, ContinuousMap.coe_comp, Surjective.surj.range_comp, Set.range_comp]
  change ⇑(base_factorization h).choose.hom ''
    ((Spec R).basicOpen (r h hp)).ι.opensRange.carrier ⊆ (Opens.ι V).opensRange.carrier
  simp only [Opens.opensRange_ι]
  refine Set.image_subset_iff.mpr (exists_basicOpen_preimage_opens hp).choose_spec.right

/-- The left vertical map in the outer square of the diagram. -/
private noncomputable def e' (hp : desc p ∈ V) :
    pullback (ιᵣ h hp) (Spec.map f) ⟶ Opens.toScheme V :=
  IsOpenImmersion.lift _ _ (range_ιₛ_e_subset_ιᵤ h hp)

/-- The two projections the self-pullback of `f'` followed by `ιₛ ≫ Spec.map f` are equal. -/
private lemma pullback_ιₛ_f (hp : desc p ∈ V) :
    (pullback.fst (f' h hp) (f' h hp) ≫ ιₛ h hp) ≫ Spec.map f =
    (pullback.snd (f' h hp) (f' h hp) ≫ ιₛ h hp) ≫ Spec.map f := by
  simp only [f', ιₛ, Category.assoc, ← pullback.condition]
  simp only [← Category.assoc, ← pullback.condition]

/-- The underlying ring map for the left vertical map `desc'` in the bottom square
(to be constructed below). -/
private noncomputable def Γdesc' (hp : desc p ∈ V) :
    Γ(Opens.toScheme V, ⊤) ⟶ Γ(((Spec R).basicOpen (r h hp)).toScheme, ⊤) := by
  apply Fork.IsLimit.lift (CommRingCat.Equalizer.isLimitForkPushoutSelfOfFaithfullyFlat
    (Γ.map (f' h hp).op) (appTopfaithfullyFlat h hp)) (Γ.map (e' h hp).op)
  have : IsIso (pushoutComparison Γ (f' h hp).op (f' h hp).op) := by infer_instance
  apply this.mono_of_iso.right_cancellation
  simp only [Category.assoc, inl_comp_pushoutComparison, ← Functor.map_comp,
    inr_comp_pushoutComparison]
  congr 1
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, ← pullbackIsoUnopPushout_inv_fst, Quiver.Hom.unop_op, Category.assoc,
    ← pullbackIsoUnopPushout_inv_snd]
  congr 1
  apply (cancel_mono (ιᵤ V)).mp
  rw [e', Category.assoc, Category.assoc, IsOpenImmersion.lift_fac, ← Category.assoc,
    ← Category.assoc, ← pullback.lift_fst _ _ (pullback_ιₛ_f h hp).symm]
  nth_rw 1 [← pullback.lift_snd _ _ (pullback_ιₛ_f h hp).symm]
  exact congrArg (_ ≫ ·) h.symm

/-- The outer square is commutative. -/
private lemma e'_ιᵤ_eq_ιₛ_e (hp : desc p ∈ V) : e' h hp ≫ ιᵤ V = ιₛ h hp ≫ e :=
  IsOpenImmersion.lift_fac (ιᵤ V) (ιₛ h hp ≫ e) (range_ιₛ_e_subset_ιᵤ h hp)

/-- The left vertical map in the bottom square. -/
private noncomputable def desc' (hp : desc p ∈ V) [hV : IsAffine V] :
    ((Spec R).basicOpen (r h hp)).toScheme ⟶ V.toScheme :=
  ((Spec R).basicOpen _).toScheme.isoSpec.hom ≫ Spec.map (Γdesc' h hp) ≫ V.toScheme.isoSpec.inv

/-- Compatibility of left vertical maps: inner composition equals outer. -/
private lemma desc'_comp (hp : desc p ∈ V) [IsAffine V] : f' h hp ≫ desc' h hp = e' h hp := by
  apply ext_of_isAffine
  have : Γdesc' h hp ≫ (f' h hp).appTop = (e' h hp).appTop := Fork.IsLimit.lift_ι'
    (CommRingCat.Equalizer.isLimitForkPushoutSelfOfFaithfullyFlat _ (appTopfaithfullyFlat h hp)) _ _
  rw [comp_appTop, ← this]
  congr 1
  simp only [desc', ← IsIso.Iso.inv_hom, comp_appTop, inv_appTop, Category.assoc]
  apply (Iso.inv_comp_eq (asIso _)).mpr
  simp only [isoSpec_hom, toSpecΓ_appTop, ΓSpecIso_naturality, asIso_hom]

open IsPullback in
/-- Two different expressions of the canonical map `P ×[Spec R] P_q ⟶ W ×[Spec R] W_q`, where
`P_q` and `W_q` denote `P` and `W` applied to another point `q : Spec R` and a neighborhood `V'`. -/
private lemma pullback_lift_paste_horiz
    (hp : desc p ∈ V) {V' : U.Opens} {q : Spec R} (hq : desc q ∈ V') :
    pullback.lift (f := ιᵣ h hp) (g := ιᵣ h hq)
      (pullback.fst (f' h hp ≫ ιᵣ h hp) (f' h hq ≫ ιᵣ h hq) ≫ f' h hp)
      (pullback.snd (f' h hp ≫ ιᵣ h hp) (f' h hq ≫ ιᵣ h hq) ≫ f' h hq)
      (by simp [pullback.condition]) =
    (paste_horiz (of_hasPullback _ _)
      (paste_vert (of_hasPullback _ _) (of_hasPullback _ _))).isoPullback.inv ≫
    pullback.fst (pullback.snd _ _ ≫ pullback.snd _ _) _ ≫ pullback.snd _ _ := by
  apply (@cancel_mono _ _ _ _ _ (pullback.fst (ιᵣ h hp) (ιᵣ h hq)) ?_).mp ?_
  · simp only [ιᵣ]
    infer_instance
  · simp only [pullback.lift_fst, Category.assoc, ← pullback.condition]
    rw [← Category.assoc (pullback.fst _ _) _ _, ← Category.assoc, isoPullback_inv_fst]

/-- The two pullback projections from `W ×[Spec R] W_q` become equal after composed with the scheme
map to `U`, where `W_q` denotes `W` applied to another point `q : Spec R`. -/
private lemma desc'_cocycle_condition (hp : desc p ∈ V) [hV : IsAffine V]
    {V' : U.Opens} {q : Spec R} (hq : desc q ∈ V') [hV' : IsAffine V'] :
    pullback.fst (ιᵣ h hp) (ιᵣ h hq) ≫ desc' h hp ≫ ιᵤ V =
      pullback.snd (ιᵣ h hp) (ιᵣ h hq) ≫ desc' h hq ≫ ιᵤ V' := by
  apply (@cancel_epi _ _ _ _ _ (pullback.lift (f := ιᵣ h hp) (g := ιᵣ h hq)
    (pullback.fst (f' h hp ≫ ιᵣ h hp) (f' h hq ≫ ιᵣ h hq) ≫ f' h hp)
    (pullback.snd (f' h hp ≫ ιᵣ h hp) (f' h hq ≫ ιᵣ h hq) ≫ f' h hq)
    (by simp [pullback.condition])) ?_).mp ?_
  · rw [pullback_lift_paste_horiz h hp hq]
    simp only [ιᵣ, f', Flat.epi_of_flat_of_surjective]
  · simp only [← Category.assoc, pullback.lift_fst, pullback.lift_snd]
    simp only [Category.assoc, desc'_comp, e', IsOpenImmersion.lift_fac]
    rw [← Category.assoc, ← Category.assoc, ← pullback.lift_fst (f := Spec.map f) (g := Spec.map f)
      (pullback.fst (f' h hp ≫ ιᵣ h hp) (f' h hq ≫ ιᵣ h hq) ≫ ιₛ h hp)
      (pullback.snd (f' h hp ≫ ιᵣ h hp) (f' h hq ≫ ιᵣ h hq) ≫ ιₛ h hq)
      (by simp [ιₛ, f', ← pullback.condition])]
    nth_rw 2 [← pullback.lift_snd (f := Spec.map f) (g := Spec.map f)
      (pullback.fst (f' h hp ≫ ιᵣ h hp) (f' h hq ≫ ιᵣ h hq) ≫ ιₛ h hp)
      (pullback.snd (f' h hp ≫ ιᵣ h hp) (f' h hq ≫ ιᵣ h hq) ≫ ιₛ h hq)
      (by simp [ιₛ, f', ← pullback.condition])]
    simp only [Category.assoc]
    congr 1

/-- An open cover of `Spec R` by basic open subsets that maps to affine open subsets in `U` under
`(base_factorization h).choose : (Spec R).carrier ⟶ U.carrier`. -/
private noncomputable def coverR : (Spec R).OpenCover := by
  apply Scheme.openCoverOfIsOpenCover (Spec R) <| fun p ↦ ((Spec R).basicOpen
    (exists_basicOpen_preimage_opens (U.local_affine (desc p)).choose.property).choose)
  apply TopologicalSpace.Opens.coe_eq_univ.mp (Set.eq_univ_iff_forall.mpr ?_)
  intro p
  apply TopologicalSpace.Opens.mem_iSup.mpr
  exact ⟨p,
    (exists_basicOpen_preimage_opens (U.local_affine (desc p)).choose.property).choose_spec.left⟩

/-- An open cover of `Spec R` by basic open subsets that maps to affine open subsets in `U` under
`(base_factorization h).choose : (Spec R).carrier ⟶ U.carrier`. -/
private noncomputable def coverR' : (Spec R).OpenCover := by
  apply Scheme.openCoverOfIsOpenCover (Spec R) <| fun p ↦ ((Spec R).basicOpen
    (r h (exists_isAffineOpen_mem_and_subset
      (TopologicalSpace.Opens.mem_top (desc p))).choose_spec.right.left))
  apply TopologicalSpace.Opens.coe_eq_univ.mp (Set.eq_univ_iff_forall.mpr ?_)
  intro p
  apply TopologicalSpace.Opens.mem_iSup.mpr
  exact ⟨p, (exists_basicOpen_preimage_opens (exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top (desc p))).choose_spec.right.left).choose_spec.left⟩

instance Scheme.isAffine_local_affine {X : Scheme.{u}} (x : X) :
    IsAffine (Scheme.Opens.toScheme (X.local_affine x).choose.obj) := by
  let f : Scheme.Opens.toScheme (X.local_affine x).choose.obj ≅
      AlgebraicGeometry.Spec (X.local_affine x).choose_spec.choose :=
    Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimageIso
      (X.local_affine x).choose_spec.choose_spec.some
  exact IsAffine.of_isIso f.hom

/-- The fpqc descent morphism `Spec R ⟶ U` of schemes obtained from a morphism `e : Spec S ⟶ U` of
schemes which coequalizes the two projections of the self-pullback of `Spec S ⟶ Spec R`. -/
noncomputable def descSpec : Spec R ⟶ U :=
  (coverR h).glueMorphisms
    (fun x ↦ desc' h (U.local_affine (desc x)).choose.property ≫
      ιᵤ (U.local_affine (desc x)).choose.obj)
    (fun x y ↦ desc'_cocycle_condition h
      (U.local_affine ((base_factorization h).choose x)).choose.property
      (U.local_affine ((base_factorization h).choose y)).choose.property)

/-- The fpqc descent morphism `Spec R ⟶ U` of schemes obtained from a morphism `e : Spec S ⟶ U` of
schemes which coequalizes the two projections of the self-pullback of `Spec S ⟶ Spec R`. -/
noncomputable def descSpec' : Spec R ⟶ U :=
  (coverR' h).glueMorphisms
    (fun p ↦ desc' h (exists_isAffineOpen_mem_and_subset
      (TopologicalSpace.Opens.mem_top (desc p))).choose_spec.right.left
      (hV := (exists_isAffineOpen_mem_and_subset
        (TopologicalSpace.Opens.mem_top (desc p))).choose_spec.left)
      ≫ ιᵤ (exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top (desc p))).choose)
    (fun p q ↦ by
      exact desc'_cocycle_condition h
        (hV := (exists_isAffineOpen_mem_and_subset
          (TopologicalSpace.Opens.mem_top (desc p))).choose_spec.left)
        (hV' := (exists_isAffineOpen_mem_and_subset
          (TopologicalSpace.Opens.mem_top (desc q))).choose_spec.left)
        (exists_isAffineOpen_mem_and_subset
          (TopologicalSpace.Opens.mem_top (desc p))).choose_spec.right.left
        (exists_isAffineOpen_mem_and_subset
          (TopologicalSpace.Opens.mem_top (desc q))).choose_spec.right.left)

end Spec

section DescSpec

variable {R S : CommRingCat.{u}} {f : R ⟶ S}
variable [Flat (Spec.map f)] [Surjective (Spec.map f)]
variable {U : Scheme.{u}} {e : Spec S ⟶ U}
  (h : pullback.fst (Spec.map f) (Spec.map f) ≫ e = pullback.snd (Spec.map f) (Spec.map f) ≫ e)

/-- `descSpec` composed with `Spec.map f` recovers the original morphism `e`. -/
lemma descSpec_comp : Spec.map f ≫ descSpec h = e := by
  apply Cover.hom_ext (Precoverage.ZeroHypercover.pullback₂ (Spec.map f) (coverR h))
  intro p
  simp only [Precoverage.ZeroHypercover.pullback₂, PreZeroHypercover.pullback₂]
  change _ = ιₛ h (U.local_affine ((Flat.base_factorization h).choose p)).choose.property ≫ e
  rw [← e'_ιᵤ_eq_ιₛ_e, ← desc'_comp, ← Category.assoc, ← pullback.condition, Category.assoc]
  exact congrArg (_ ≫ ·) (Cover.ι_glueMorphisms (coverR h) _ _ p)

/-- `descSpec` composed with `Spec.map f` recovers the original morphism `e`. -/
lemma descSpec_comp' : Spec.map f ≫ descSpec' h = e := by
  apply Cover.hom_ext (Precoverage.ZeroHypercover.pullback₂ (Spec.map f) (coverR' h))
  intro p
  change _ = ιₛ h (exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top
    ((Flat.base_factorization h).choose p))).choose_spec.right.left ≫ e
  have : IsAffine _ := (exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top
    ((base_factorization h).choose p))).choose_spec.left
  simp only [Precoverage.ZeroHypercover.pullback₂, PreZeroHypercover.pullback₂, ← e'_ιᵤ_eq_ιₛ_e]
  rw [← desc'_comp, ← Category.assoc, ← pullback.condition]
  rw [Category.assoc _ _ (descSpec' h)]
  exact congrArg (_ ≫ ·) (Cover.ι_glueMorphisms (coverR' h) _ _ p)

/-- The continuous map underlying `descSpec`. -/
lemma descSpec_base : (descSpec h).base = (Flat.base_factorization h).choose :=
  (Flat.base_factorization h).choose_spec.right (descSpec h).base
    ((Hom.comp_base _ _).symm.trans (congrArg (fun f ↦ f.base) (descSpec_comp h)))

/-- The continuous map underlying `descSpec`. -/
lemma descSpec_base' : (descSpec' h).base = (Flat.base_factorization h).choose :=
  (Flat.base_factorization h).choose_spec.right (descSpec' h).base
    ((Hom.comp_base _ _).symm.trans (congrArg (fun f ↦ f.base) (descSpec_comp' h)))

/-- `descSpec` is the unique morphism `Spec R ⟶ U` through which `e` factors. -/
lemma descSpec_unique (t : Spec R ⟶ U) (ht : Spec.map f ≫ t = e) : t = descSpec h := by
  apply Cover.hom_ext (coverR h)
  intro p
  have : Epi (pullback.snd (Spec.map f) ((coverR h).f p)) :=
    Flat.epi_of_flat_of_surjective _
  apply (cancel_epi (pullback.snd (Spec.map f) ((coverR h).f p))).mp
  rw [← Category.assoc, ← Category.assoc, ← pullback.condition, Category.assoc, Category.assoc,
    ht, descSpec_comp h]

/-- `descSpec` is the unique morphism `Spec R ⟶ U` through which `e` factors. -/
lemma descSpec_unique' (t : Spec R ⟶ U) (ht : Spec.map f ≫ t = e) : t = descSpec' h := by
  apply Cover.hom_ext (coverR' h)
  intro p
  have : Epi (pullback.snd (Spec.map f) ((coverR' h).f p)) :=
    Flat.epi_of_flat_of_surjective _
  apply (cancel_epi (pullback.snd (Spec.map f) ((coverR' h).f p))).mp
  rw [← Category.assoc, ← Category.assoc, ← pullback.condition, Category.assoc, Category.assoc,
    ht, descSpec_comp' h]

end DescSpec

section Spec

variable {R S : CommRingCat.{u}} (f : R ⟶ S)
variable (hf : f.hom.Flat) (hs : Surjective (Spec.map f))

/-- The cofork formed by the two projections  `(Spec S) ×[Spec R] (Spec S) ⟶ Spec S` followed by
`Spec S ⟶ Spec R` is a colimit when `f : R ⟶ S` is a flat ring map with surjective `Spec.map f`. -/
noncomputable def pullbackCoforkIsColimit :
    IsColimit (Cofork.ofπ (Spec.map f) pullback.condition) := by
  apply Cofork.IsColimit.mk'
  intro s
  have : Flat (Spec.map f) := HasRingHomProperty.Spec_iff.mpr hf
  use Flat.descSpec s.condition
  constructor
  · simp only [Cofork.π_ofπ, Flat.descSpec_comp s.condition]
  · intro t ht
    exact Flat.descSpec_unique s.condition t ht

/-- A regular epimorphism structure on `Spec.map f` given by the projections of the self-pullback of
`Spec.map f`, when `f : R ⟶ S` is a flat ring map with surjective `Spec.map f`. -/
noncomputable def regularEpiOfFlatOfSurjective : RegularEpi (Spec.map f) where
  W := pullback (Spec.map f) (Spec.map f)
  left := pullback.fst (Spec.map f) (Spec.map f)
  right := pullback.snd (Spec.map f) (Spec.map f)
  w := pullback.condition
  isColimit := pullbackCoforkIsColimit f hf hs

/-- An effective epimorphism structure on `Spec.map f` when `f : R ⟶ S` is a flat ring map with
surjective `Spec.map f`. -/
noncomputable def effectiveEpiStructOfFlatOfSurjective : EffectiveEpiStruct (Spec.map f) :=
  @effectiveEpiStructOfRegularEpi _ _ _ _ _ (regularEpiOfFlatOfSurjective f hf hs)

/-- `Spec.map f` is an effective epimorphism in the category of schemes when `f : R ⟶ S` is a flat
ring map with surjective `Spec.map f`. -/
@[stacks 023Q]
lemma effectiveEpi_of_flat_of_surjective (hf : f.hom.Flat) (hs : Surjective (Spec.map f)) :
    EffectiveEpi (Spec.map f) :=
  ⟨⟨effectiveEpiStructOfFlatOfSurjective f hf hs⟩⟩

end Spec

end Flat

end AlgebraicGeometry
