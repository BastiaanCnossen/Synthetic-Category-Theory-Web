# The triangle transformations of adjoint sections

For a left adjoint section, both occurrences of the unit in the triangle
identities are invertible. The corresponding counit transformations
are their one-sided inverses and hence are invertible too. Dually, a
right adjoint section has invertible triangle transformations on both
sides. This is a consequence of the triangle identities, without an
objectwise detection principle.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.SectionTriangleInverses
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.AdjointSections 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ExpressionOperations 𝒯 M ℱ P I E S
  using (retarget-invertible; post-invertible; restrict-invertible)
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ExpressionInverseLaws 𝒯 M ℱ P I E S Q
  using (module Inverses)

module Left {C D : CAT} {f : MAP C D} {s : MAP D C} (w : LeftAdjointSection f s) where
  private module W = LeftAdjointSection w
  private module A = Adjunction W.adjunction

  left-unit-invertible : IsInvertibleExpression A.left-unit
  left-unit-invertible = retarget-invertible (post-expression s A.unit)
    (comp-unitʳ s) ((comp-assoc s f s) ⁻¹) (post-invertible s A.unit W.unit-invertible)

  right-unit-invertible : IsInvertibleExpression A.right-unit
  right-unit-invertible = retarget-invertible (restrict-expression A.unit f)
    (comp-unitˡ f) (idIso ((f ∘ s) ∘ f)) (restrict-invertible A.unit f W.unit-invertible)

  left-counit-invertible : IsInvertibleExpression A.left-counit
  left-counit-invertible = Inverses.any-left-inverse-invertible
    A.left-unit left-unit-invertible A.left-counit A.left-triangle

  right-counit-invertible : IsInvertibleExpression A.right-counit
  right-counit-invertible = Inverses.any-left-inverse-invertible
    A.right-unit right-unit-invertible A.right-counit A.right-triangle

module Right {C D : CAT} {f : MAP C D} {s : MAP D C} (w : RightAdjointSection f s) where
  private module W = RightAdjointSection w
  private module A = Adjunction W.adjunction

  left-counit-invertible : IsInvertibleExpression A.left-counit
  left-counit-invertible = retarget-invertible (restrict-expression A.counit f)
    (idIso ((f ∘ s) ∘ f)) (comp-unitˡ f) (restrict-invertible A.counit f W.counit-invertible)

  right-counit-invertible : IsInvertibleExpression A.right-counit
  right-counit-invertible = retarget-invertible (post-expression s A.counit)
    ((comp-assoc s f s) ⁻¹) (comp-unitʳ s) (post-invertible s A.counit W.counit-invertible)

  left-unit-invertible : IsInvertibleExpression A.left-unit
  left-unit-invertible = Inverses.any-right-inverse-invertible
    A.left-counit left-counit-invertible A.left-unit A.left-triangle

  right-unit-invertible : IsInvertibleExpression A.right-unit
  right-unit-invertible = Inverses.any-right-inverse-invertible
    A.right-counit right-counit-invertible A.right-unit A.right-triangle
```
