import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

open CategoryTheory

namespace CategoryTheory.Limits

universe w' w v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : Type w} [Category.{w'} J]
variable {K : J ⥤ C}
variable (e : C ≌ D)

#check IsColimit

def cc (t : Cocone e.functor) (h : IsColimit t) : IsColimit  := 1

end CategoryTheory.Limits
