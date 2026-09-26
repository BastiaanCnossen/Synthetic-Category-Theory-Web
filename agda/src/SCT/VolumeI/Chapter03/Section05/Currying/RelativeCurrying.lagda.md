# Relative currying with native triangles

The mapping-anima universal property gives factorization and reflection
for native functors over a base. First compute the actual uncurrying
functor on named triangles, using the base-change and postcomposition
computations. These retain the triangle over the base throughout.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.Currying.RelativeCurrying
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.NamingComparisons 𝒯 M ℱ P using (module Triangles)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.Identifications 𝒯 M ℱ P using (module Change)
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.Currying.RelativeTransposition 𝒯 M ℱ P using (module Transpose)

open import SCT.VolumeI.Chapter03.Section05.BaseChange.BaseChangeNativePoints 𝒯 M ℱ P using (module BaseChangePoints)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BaseChange 𝒯 M ℱ P using (module BaseChange)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.Postcomposition 𝒯 M ℱ P using (module Postcompose)

module Currying {S T C : CAT} (p : MAP S T) (f : MAP C S) (Π : DependentProduct p f) where
  g = DependentProduct.projection Π
  ε = DependentProduct.evaluation Π

  evaluate : {E : CAT} {t : MAP E T} → FunctorOver t g → FunctorOver (pullback₂ {f = t} {p}) f
  evaluate u = compose-over ε (Change.functor p u)

  Computation : Set (c Agda.Primitive.⊔ m)
  Computation = {E : CAT} (t : MAP E T) (u : FunctorOver t g) →
    (RelativeCurrying.At.uncurry p f Π t ∘ Over.name-over t g u) =₁
      Over.name-over (pullback₂ {f = t} {p}) f (evaluate u)

  abstract
    named-computation : Computation
    named-computation t u = Postcompose.on-named-points (pullback₂ {f = t} {p}) ε (Change.functor p u) ∙
      ((Postcompose.maps (pullback₂ {f = t} {p}) ε ◁ BaseChangePoints.on-named-points p t g u) ∙
        comp-assoc (Over.name-over t g u) (BaseChange.maps p t g)
          (Postcompose.maps (pullback₂ {f = t} {p}) ε))

  module FromComputation (computation : Computation) where
    factor : {E : CAT} (t : MAP E T) → FunctorOver (pullback₂ {f = t} {p}) f → FunctorOver t g
    factor t u = Transpose.over p f Π t u

    abstract
      factor-β : {E : CAT} (t : MAP E T) (u : FunctorOver (pullback₂ {f = t} {p}) f) →
        FunctorOverIso (evaluate (factor t u)) u
      factor-β t u = Triangles.identify-native (pullback₂ {f = t} {p}) f (evaluate (factor t u)) u
        (Transpose.comparison p f Π t u ∙ (computation t (factor t u)) ⁻¹)

      reflect : {E : CAT} (t : MAP E T) (u v : FunctorOver t g) →
        FunctorOverIso (evaluate u) (evaluate v) → FunctorOverIso u v
      reflect t u v Φ = Triangles.identify-native t g u v
        (RelativeCurrying.At.reflect p f Π t (Over.name-over t g u) (Over.name-over t g v)
          ((computation t v) ⁻¹ ∙
            (Triangles.Identification.identification (pullback₂ {f = t} {p}) f (evaluate u) (evaluate v) Φ ∙
              computation t u)))

      evaluate-identity : FunctorOverIso (evaluate (identity-over g)) ε
      evaluate-identity = compose-iso-over (right-unit-over ε)
        (postwhisker-over ε (Change.Identity.comparison p g))

      evaluate-composite : {B D : CAT} {s : MAP B T} {t : MAP D T}
        (u : FunctorOver s t) (v : FunctorOver t g) →
        FunctorOverIso (evaluate (compose-over v u)) (compose-over (evaluate v) (Change.functor p u))
      evaluate-composite u v = compose-iso-over
        (inverse-iso-over (associator-over (Change.functor p u) (Change.functor p v) ε))
        (postwhisker-over ε (inverse-iso-over (Change.Composite.comparison p u v)))
  module Native = FromComputation named-computation
```
