# Hom categories as fibers of iterated coslices

Fix an object u of C under x and write y for its target. Triangles from
u whose target arrow ends at z form the pullback of the iterated-coslice
projection along the hom-fiber inclusion. Flattening identifies this
pullback with Hom(y,z). The right leg is the specified hom-precomposition
by the hom point represented by u; all projection identifications remain
part of the square.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares

module SCT.VolumeI.Chapter04.Section03.CosliceTriangleHomFibers
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section06.HomComposition 𝒯 M ℱ P I E S public hiding (module At)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (Cone; ConeIso; IsPullback; coneRetarget; coneRetarget-β; pullback-cone-invariant)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P using (degenerate-pullback)
import SCT.VolumeI.Chapter04.Section03.IteratedCoslicePrecomposition as Flattening
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceObjectPrecomposition as ObjectPrecomposition
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceFiberPrecomposition as HomPrecomposition
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanPullbacks as Cospans
open Laws.PullbackStructure P using (Pullback; pullbackLift; pullbackLift-β)

module At {C : CAT} (x : Obj-abs C) (u : Obj-abs (Coslice C x)) (z : Obj-abs C) where
  y = coslice-projection x ∘ u
  private
    V = Coslice C x
    U = Coslice V u
    Y = Coslice C y
    π = coslice-projection u
    module Flatten = Flattening.At 𝒯 M ℱ P I E S Q x u using (functor; isEquiv; projection)
    module Object = ObjectPrecomposition.At 𝒯 M ℱ P I E S x u using (hom-point; standard-precompose; standard-comparison)
    module Fiber = HomPrecomposition.Along 𝒯 M ℱ P I E S
      {C = C} {x = x} {y = y} Object.hom-point z
      using (square; square-isPullback; source-inclusion; target-inclusion; hom-precompose)
    r = Object.standard-precompose
    j = IsEquiv.inverse Flatten.isEquiv
    α : (r ∘ Flatten.functor) =₁ π
    α = Flatten.projection ∙ (Object.standard-comparison ▷ Flatten.functor) ⁻¹
    inverse-projection : (π ∘ j) =₁ r
    inverse-projection = comp-unitʳ r ∙
      ((r ◁ (IsEquiv.retractionIso Flatten.isEquiv) ⁻¹) ∙
        (comp-assoc j Flatten.functor r ∙ (α ▷ j) ⁻¹))
    inverse-isEquiv : IsEquiv j
    inverse-isEquiv = record { inverse = Flatten.functor
      ; sectionIso = IsEquiv.retractionIso Flatten.isEquiv
      ; retractionIso = IsEquiv.sectionIso Flatten.isEquiv }

  hom-point = Object.hom-point
  inclusion = Fiber.target-inclusion
  triangles : CAT
  triangles = Pullback π inclusion
  triangle : MAP (Hom C y z) U
  triangle = j ∘ Fiber.source-inclusion
  precompose = Fiber.hom-precompose

  cospan : CospanMap r inclusion π inclusion
  cospan = record { left = j ; right = id (Hom C x z) ; base = id V
    ; leftSquare = (comp-unitˡ r) ⁻¹ ∙ inverse-projection
    ; rightSquare = (comp-unitˡ inclusion) ⁻¹ ∙ comp-unitʳ inclusion }
  private
    mapped = CospanMap.mapCone cospan Fiber.square
    module Preserved = Cospans.Mapped 𝒯 P cospan
      (degenerate-pullback (id-isEquiv V) (Cospans.rightSquareOf 𝒯 P cospan) (id-isEquiv (Hom C x z)))
      Fiber.square Fiber.square-isPullback using (isPullback)

  square : Cone π inclusion (Hom C y z)
  square = coneRetarget mapped triangle precompose (idIso triangle) (comp-unitˡ precompose)
  comparison : ConeIso mapped square
  comparison = coneRetarget-β mapped triangle precompose (idIso triangle) (comp-unitˡ precompose)
  abstract
    square-isPullback : IsPullback square
    square-isPullback = pullback-cone-invariant comparison (Preserved.isPullback inverse-isEquiv)

  hom-to-triangles : MAP (Hom C y z) triangles
  hom-to-triangles = pullbackLift square
  hom-to-triangles-isEquiv : IsEquiv hom-to-triangles
  hom-to-triangles-isEquiv = square-isPullback
  hom-to-triangles-computation = pullbackLift-β square
```
