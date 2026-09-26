# Separating the two inverse triangles

The definition of `Iso C` first matches the short edges and then makes
both long edges constant. Products of pullbacks and the diagonal
description let us impose these conditions in the opposite order.
The equivalence below retains the two centers in their specified reversed
order and uses the full pullback comparisons at each step.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section03.PullbackCalculus.InversePullbackComparison
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section03.Isomorphisms 𝒯 M ℱ P I E
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M using (productMap-pair)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.Cospans.CospanEquivalences 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullbackSwap; pullbackSwap-isEquiv)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange 𝒯 using (changeLeft)
import SCT.VolumeI.Chapter01.Section06.Pasting.UniversalNestedPullbacks as Nested
open import SCT.VolumeI.Chapter01.Section06.Coordinates.DiagonalPullbacks 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.Coordinates.ProductPullbacks 𝒯 P

projection-after : {W X Y Z : CAT} (h : MAP X Y) (π : MAP Y Z)
  {p : MAP X Z} → (π ∘ h) =₁ p → (k : MAP W X) → (π ∘ (h ∘ k)) =₁ (p ∘ k)
projection-after h π β k = (β ▷ k) ∙ (comp-assoc k h π) ⁻¹

module InverseComparison (C : CAT) where
  T = Triangles C
  H = Ar C
  A = InverseTriangles C
  J = Pullback (edge₁ {C}) identityArrow
  forget : MAP J T
  forget = pullback₁
  r l : MAP J H
  r = edge₀ ∘ forget
  l = edge₂ ∘ forget
  a-pair : MAP A (T × T)
  a-pair = pair pullback₁ pullback₂
  u : MAP (J × J) (T × T)
  u = productMap forget forget
  long : MAP (T × T) (H × H)
  long = productMap (edge₁ {C}) edge₁
  identities : MAP (C × C) (H × H)
  identities = productMap (identityArrow {C}) (identityArrow {C})
  short : MAP (T × T) (H × H)
  short = productMap (edge₀ {C}) edge₂
  Δ : MAP H (H × H)
  Δ = pair (id H) (id H)

  normalization : CospanMap (inverseLongEdges C) (inverseIdentityEdges C)
    (long ∘ a-pair) identities
  normalization = record
    { left = id A ; right = swap {C} {C} ; base = id (H × H)
    ; leftSquare = (comp-unitˡ (inverseLongEdges C)) ⁻¹ ∙
        (productMap-pair edge₁ edge₁ pullback₁ pullback₂ ∙ comp-unitʳ (long ∘ a-pair))
    ; rightSquare = (comp-unitˡ (inverseIdentityEdges C)) ⁻¹ ∙
        productMap-pair identityArrow identityArrow pr₂ pr₁ }
  module Normalize = CospanMap normalization using (pullbackMap; mapCone)
  opaque
    normalization-isEquiv : IsEquiv Normalize.pullbackMap
    normalization-isEquiv = CospanEquivalence.pullbackMap-isEquiv
      normalization (id-isEquiv A) (swap-isEquiv C C) (id-isEquiv (H × H))

  module LongProduct = Product (pullbackCone (edge₁ {C}) identityArrow)
    (pullbackCone (edge₁ {C}) identityArrow)
    (pullbackCone-isPullback edge₁ identityArrow) (pullbackCone-isPullback edge₁ identityArrow)
    using (square; square-isPullback)
  module LongOrder = Nested.Nested 𝒯 P a-pair long identities
    LongProduct.square LongProduct.square-isPullback
    using (insert; insert-isEquiv; r; ℓ; ρ; insertionCone)
  module ShortDiagonal = DiagonalPullback (edge₀ {C}) edge₂ using (module Universal)
  module ShortSquare = ShortDiagonal.Universal (pullbackCone (edge₀ {C}) edge₂)
    (pullbackCone-isPullback edge₀ edge₂)
    using (direct; isPullback)
  module ShortOrder = Nested.Nested 𝒯 P u short Δ ShortSquare.direct ShortSquare.isPullback
    using (flatten; flatten-isEquiv; flatCone)
  module ShortChange = ChangeLeft (productMap-comp forget edge₀ forget edge₂) Δ
    using (forward; forward-isEquiv)
  module ResultDiagonal = DiagonalPullback r l using (forward; forward-isEquiv; forward-left)

  first-stage : MAP (Iso C) (Pullback a-pair u)
  first-stage = LongOrder.insert ∘ Normalize.pullbackMap
  second-stage : MAP (Iso C) (Pullback u a-pair)
  second-stage = pullbackSwap a-pair u ∘ first-stage
  third-stage : MAP (Iso C) (Pullback (short ∘ u) Δ)
  third-stage = ShortOrder.flatten ∘ second-stage
  diagonal-stage : MAP (Iso C) (Pullback (productMap r l) Δ)
  diagonal-stage = ShortChange.forward ∘ third-stage

  opaque
    first-stage-isEquiv : IsEquiv first-stage
    first-stage-isEquiv = equiv-compose Normalize.pullbackMap LongOrder.insert
      normalization-isEquiv LongOrder.insert-isEquiv
    second-stage-isEquiv : IsEquiv second-stage
    second-stage-isEquiv = equiv-compose first-stage (pullbackSwap a-pair u)
      first-stage-isEquiv (pullbackSwap-isEquiv a-pair u)
    third-stage-isEquiv : IsEquiv third-stage
    third-stage-isEquiv = equiv-compose second-stage ShortOrder.flatten second-stage-isEquiv ShortOrder.flatten-isEquiv
    diagonal-stage-isEquiv : IsEquiv diagonal-stage
    diagonal-stage-isEquiv = equiv-compose third-stage ShortChange.forward third-stage-isEquiv ShortChange.forward-isEquiv

  chosen = equiv-lift ResultDiagonal.forward-isEquiv diagonal-stage
  comparison : MAP (Iso C) (Pullback r l)
  comparison = FunctorLift.lift chosen
  comparison-isEquiv : IsEquiv comparison
  comparison-isEquiv = equiv-cancel-left comparison ResultDiagonal.forward ResultDiagonal.forward-isEquiv
    (equiv-transport ((FunctorLift.comparison chosen) ⁻¹) diagonal-stage-isEquiv)

  square : Cone r l (Iso C)
  square = conePre comparison (pullbackCone r l)
  square-isPullback : IsPullback square
  square-isPullback = pullback-restrict-equivalence (pullbackCone r l) comparison
    (pullbackCone-isPullback r l) comparison-isEquiv

  pair-witnesses : (pair (pullback₁ {f = r} {l}) pullback₂ ∘ comparison) =₁
    (LongOrder.r ∘ first-stage)
  pair-witnesses =
    projection-after (pullbackSwap a-pair u) pullback₁
      (pullbackLift-β₁ (coneSwap (pullbackCone a-pair u))) first-stage ∙
    (projection-after ShortOrder.flatten pullback₁ (pullbackLift-β₁ ShortOrder.flatCone) second-stage ∙
    (projection-after ShortChange.forward pullback₁
      (pullbackLift-β₁ (changeLeft (productMap-comp forget edge₀ forget edge₂)
        (pullbackCone (short ∘ u) Δ))) third-stage ∙
    ((pullback₁ ◁ FunctorLift.comparison chosen) ∙
      (projection-after ResultDiagonal.forward pullback₁ ResultDiagonal.forward-left comparison) ⁻¹)))

  original-triangles : (LongOrder.ℓ ∘ first-stage) =₁ (isoTriangles {C})
  original-triangles = comp-unitˡ isoTriangles ∙
    (pullbackLift-β₁ (Normalize.mapCone (pullbackCone (inverseLongEdges C) (inverseIdentityEdges C))) ∙
      projection-after LongOrder.insert LongOrder.ℓ
        (pullbackLift-β₁ LongOrder.insertionCone) Normalize.pullbackMap)

  forget-witnesses : (u ∘ (pair (pullback₁ {f = r} {l}) pullback₂ ∘ comparison)) =₁
    (a-pair ∘ isoTriangles)
  forget-witnesses = (a-pair ◁ original-triangles) ∙
    (comp-assoc first-stage LongOrder.ℓ a-pair ∙
    ((LongOrder.ρ ⁻¹ ▷ first-stage) ∙
    ((comp-assoc first-stage LongOrder.r u) ⁻¹ ∙ (u ◁ pair-witnesses))))

  first-triangle : (forget ∘ (pullback₁ ∘ comparison)) =₁
    (pullback₁ {f = edge₀ {C}} {edge₂} ∘ isoTriangles)
  first-triangle = project-pair₁ pullback₁ pullback₂ isoTriangles ∙
    ((pr₁ ◁ forget-witnesses) ∙ before ⁻¹)
    where
    before = (forget ◁ project-pair₁ (pullback₁ {f = r} {l}) pullback₂ comparison) ∙
      (comp-assoc (pair (pullback₁ {f = r} {l}) pullback₂ ∘ comparison) pr₁ forget ∙
        project-pair₁ (forget ∘ pr₁) (forget ∘ pr₂)
          (pair (pullback₁ {f = r} {l}) pullback₂ ∘ comparison))

  comparison-arrow : (r ∘ Cone.left square) =₁ (isoArrow {C})
  comparison-arrow = (comp-assoc isoTriangles pullback₁ edge₀) ⁻¹ ∙
    ((edge₀ ◁ first-triangle) ∙ comp-assoc (pullback₁ ∘ comparison) forget edge₀)
```
