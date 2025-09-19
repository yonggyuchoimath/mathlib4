import Mathlib.CategoryTheory.EffectiveEpi.RegularEpi
import Mathlib.CategoryTheory.Limits.Types.Shapes

/-!

# Effective epimorphisms in the category of types

We prove that effective epimorphisms in the category of types are precisely surjective functions.
-/

namespace CategoryTheory

universe u

open Limits Function

/-- For a morphism `f : X ⟶ Y` in the category of types which is surjective as a function,
`f : X ⟶ Y` has a structure of a regular epimorphism as the coequalizer of the two projections
from `Limits.Types.PullbackObj f f` to `X`. -/
noncomputable def regularEpi_pullbackObj_of_surjective {X Y : Type u} {f : X ⟶ Y}
    (hf : Surjective f) : RegularEpi f where
  W := Types.PullbackObj f f
  left := (Types.pullbackCone f f).fst
  right := (Types.pullbackCone f f).snd
  w := funext fun p => p.2
  isColimit := by
    refine Cofork.isColimitOfIsos _
      (coequalizerIsCoequalizer (Types.pullbackCone f f).fst (Types.pullbackCone f f).snd) _
      (.refl _) (.refl _) ?_ (by simp) (by simp) ?_
    · simp only [Cofork.ofπ_pt]
      apply Types.coequalizerIso _ _ ≪≫ (Equiv.ofBijective ?_ ⟨?_, ?_⟩).toIso
      · apply Coequalizer.desc _ _ f
        simp only [← types_comp]
        exact funext fun p => p.2
      · intro z₁ z₂ h
        rw [← Quot.out_eq z₁, ← Quot.out_eq z₂]
        have h' : f (Quot.out z₁) = f (Quot.out z₂) := by
          rwa [← Coequalizer.desc_mk _ _ f _ _, ← Coequalizer.desc_mk _ _ f _ _,
            Coequalizer.mk, Coequalizer.mk, Quot.out_eq, Quot.out_eq]
        exact Quot.sound (Coequalizer.Rel.intro (Subtype.mk (Prod.mk _ _) h'))
      · intro y
        obtain ⟨x, _⟩ := hf y
        exact ⟨Quot.mk _ x, by simpa⟩
    · cat_disch

/-- For a morphism `f : X ⟶ Y` in the category of types which is surjective as a function, then
`f : X ⟶ Y` has a structure of a regular epimorphism as the coequalizer of the two projections
from `Limits.pullback f f` to `X`. -/
noncomputable def regularEpi_pullback_of_surjective {X Y : Type u} {f : X ⟶ Y} (hf : Surjective f) :
    RegularEpi f where
  W := pullback f f
  left := pullback.fst f f
  right := pullback.snd f f
  w := pullback.condition
  isColimit := Cofork.isColimitOfIsos _ (regularEpi_pullbackObj_of_surjective hf).isColimit _
    (Types.pullbackIsoPullback f f).symm (.refl X) (.refl Y)
      (by cat_disch) (by cat_disch) (by cat_disch)

/-- A morphism in the category of types has a sturcture of a regular epimorphism if and only if
it is a surjective function as types. -/
lemma regularEpi_iff_surjective {X Y : Type u} {f : X ⟶ Y} :
    Nonempty (RegularEpi f) ↔ Surjective f where
  mp := fun ⟨_⟩ => surjective_of_epi _
  mpr := fun hf => ⟨regularEpi_pullback_of_surjective hf⟩

/-- A morphism in the category of types is an effective epimorphism if and only if
it is a surjective function as types. -/
lemma effectiveEpi_iff_surjective {X Y : Type u} {f : X ⟶ Y} : EffectiveEpi f ↔ Surjective f where
  mp := fun h => regularEpi_iff_surjective.mp ⟨by infer_instance⟩
  mpr := fun h => by
    let := (regularEpi_iff_surjective.mpr h).some
    infer_instance

end CategoryTheory
