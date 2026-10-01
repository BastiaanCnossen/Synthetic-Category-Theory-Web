# Precomposition between coslices

Compose the universal arrow out of `y` with a fixed arrow from `x` to
`y`. The resulting functor from `C_{y/}` to `C_{x/}` retains the target
projection and both endpoint frames of the composite.

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

module SCT.VolumeI.Chapter04.Section03.CoslicePrecomposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section06.HomComposition 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯 using (ConeIso; conePre)
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P using (FunctorOver)

module Along {C : CAT} {x y : Obj-abs C} (e : Obj-abs (Hom C x y)) where
  private
    module Source = EndpointFiber (const y) (id C)
    module Target = EndpointFiber (const x) (id C)
    module Arrow = At e using (family)

  incoming : MorphismExpression (const {P = Coslice C y} y) Source.base
  incoming = retarget-expression Source.frame (const-pre y Source.base) (comp-unitˡ Source.base)

  composite : MorphismExpression (const {P = Coslice C y} x) Source.base
  composite = compose-expression (Arrow.family (Coslice C y)) incoming

  framed-composite : MorphismExpression ((const x) ∘ Source.base) ((id C) ∘ Source.base)
  framed-composite = retarget-expression composite
    ((const-pre x Source.base) ⁻¹) ((comp-unitˡ Source.base) ⁻¹)

  functor : MAP (Coslice C y) (Coslice C x)
  functor = Target.lift Source.base framed-composite

  computation : ConeIso
    (conePre functor (pullbackCone endpoints (pair (const x) (id C))))
    (Target.cone Source.base framed-composite)
  computation = Target.lift-β Source.base framed-composite

  over-base : FunctorOver (coslice-projection y) (coslice-projection x)
  over-base = record
    { lift = functor ; comparison = Target.lift-base Source.base framed-composite }
```
