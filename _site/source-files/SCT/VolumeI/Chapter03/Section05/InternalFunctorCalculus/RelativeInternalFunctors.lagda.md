# The relative internal functor category

The construction in `def:Relative_Functor_Category` takes the dependent
product of `D ×_S C → C` along `C → S`. Its evaluation is the dependent
product evaluation followed by the projection to `D`.

The mapping equivalence first uses the dependent-product universal
property, then the comparison for a pullback target. The specified
pullback matching changes the resulting source structure functor.
`InternalEvaluation` identifies this composite with literal base change
followed by postcomposition with `evaluation`, retaining the triangle.
`InternalFunctors` supplies the resulting construction from exponentiability.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.InternalFunctorCalculus.RelativeInternalFunctors
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.Currying.EvaluatedPullbackTargets 𝒯 M ℱ P using (module PullbackTarget)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.SourceChange 𝒯 M ℱ P using (module Change)

module Internal {C D S : CAT} (p : MAP C S) (q : MAP D S)
  (Π : DependentProduct p (pullback₂ {f = q} {p})) where

  category : CAT
  category = DependentProduct.category Π

  projection : MAP category S
  projection = DependentProduct.projection Π

  ε = DependentProduct.evaluation Π
  r : MAP (Pullback projection p) C
  r = pullback₂
  structure : MAP (Pullback projection p) S
  structure = projection ∘ pullback₁

  evaluation : MAP (Pullback projection p) D
  evaluation = pullback₁ {f = q} {p} ∘ FunctorLift.lift ε

  evaluation-over : (q ∘ evaluation) =₁ structure
  evaluation-over = pullbackMatch {f = projection} {p} ⁻¹ ∙
    ((p ◁ FunctorLift.comparison ε) ∙
      (comp-assoc (FunctorLift.lift ε) (pullback₂ {f = q} {p}) p ∙
        ((pullbackMatch {f = q} {p} ▷ FunctorLift.lift ε) ∙
          (comp-assoc (FunctorLift.lift ε) (pullback₁ {f = q} {p}) q) ⁻¹)))

  evaluation-triangle : FunctorOver structure q
  evaluation-triangle = record { lift = evaluation ; comparison = evaluation-over }

  module At {E : CAT} (t : MAP E S) where
    source-projection : MAP (Pullback t p) C
    source-projection = pullback₂
    source-structure : MAP (Pullback t p) S
    source-structure = t ∘ pullback₁
    module DP = RelativeCurrying.At p (pullback₂ {f = q} {p}) Π t
    module Target = PullbackTarget p q source-projection
    module Structure = Change (pullbackMatch {f = t} {p} ⁻¹) q

    uncurry : MAP (MapOver t projection) (MapOver source-structure q)
    uncurry = Structure.maps ∘ (Target.maps ∘ DP.uncurry)

    uncurry-isEquiv : IsEquiv uncurry
    uncurry-isEquiv = equiv-compose (Target.maps ∘ DP.uncurry) Structure.maps
      (equiv-compose DP.uncurry Target.maps DP.uncurry-isEquiv Target.maps-isEquiv)
      Structure.maps-isEquiv

    curry : MAP (MapOver source-structure q) (MapOver t projection)
    curry = IsEquiv.inverse uncurry-isEquiv

    curry-uncurry : (curry ∘ uncurry) =₁ id (MapOver t projection)
    curry-uncurry = (IsEquiv.sectionIso uncurry-isEquiv) ⁻¹

    uncurry-curry : (uncurry ∘ curry) =₁ id (MapOver source-structure q)
    uncurry-curry = (IsEquiv.retractionIso uncurry-isEquiv) ⁻¹
```
