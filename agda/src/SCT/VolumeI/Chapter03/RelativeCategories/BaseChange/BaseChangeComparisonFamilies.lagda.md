# Base change acts on the anima of relative identifications

Restrict the universal relative comparison, paste with the source
pullback matching, and transport its two endpoints through the pullback
factorizations. The isomorphism-anima universal property lifts this
whole family at once. Its right projection gives the triangle over the
new base.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.PullbackComparison as Comparison
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Parameterized as Param

module SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BaseChangeComparisonFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯 using (coneIso-inverse)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (module UniversalCone)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeIdentificationTransport 𝒯 P using (module Transport)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-inverse)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ComparisonRestriction 𝒯 M ℱ P using (module Restriction)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackTriangles 𝒯 M ℱ P using (lift-triangle)
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ComparisonLifting 𝒯 M ℱ P using (module Lift)
open Param vocabulary terminal products productLaws composition vertical
  using (const-cong; unitˡ; left-cancelʳ)

module Change {C D S T : CAT} (p : MAP S T) {f : MAP C T} {g : MAP D T}
  (u v : FunctorOver f g) where
  module Restricted = Restriction p (pullback₁ {f = f} {p}) pullback₂ pullbackMatch u v
    using (cone; cospan; module Source)
  module Encoded = Restricted.Source
  first = Restricted.cone u
  second = Restricted.cone v
  hu = pullbackLift first
  hv = pullbackLift second
  βu = pullbackLift-β₂ first
  βv = pullbackLift-β₂ second
  source = pullbackCone Encoded.leftMap Encoded.rightMap
  restricted = CospanMap.mapCone Restricted.cospan source
  module Endpoints = Transport (coneIso-inverse (pullbackLift-β first))
    (coneIso-inverse (pullbackLift-β second)) using (mapCone; module Right)
  transported = Endpoints.mapCone restricted
  module Target = Comparison.IsoComparison 𝒯 dataPullback hu hv using (comparisonCone)
  module Factor = UniversalCone Target.comparisonCone (pullback-isoMap-isEquiv hu hv)
    using (factor; factor-β)

  functor : MAP Encoded.category (hu ＝ hv)
  functor = Factor.factor transported

  opaque
    cone-computation : ConeIso (conePre functor Target.comparisonCone) transported
    cone-computation = Factor.factor-β transported

  opaque
    right-normalization : Cone.right transported =₁
      (const (βv ⁻¹) ∙ const βu)
    right-normalization = isoComp-cong (idIso (const (βv ⁻¹)))
      (unitˡ (const βu) ∙
        isoComp-cong (const-pre (idIso (pullback₂ {f = f} {p})) (Cone.right source))
          (const-cong (inverse-inverse βu))) ∙
      Endpoints.Right.evaluate (Cone.right restricted)

    family-triangle : (const βv ∙ (pullback₂ {f = g} {p} ◁ functor)) =₁ const βu
    family-triangle = left-cancelʳ βv (const βu) ∙
      isoComp-cong (idIso (const βv))
        (right-normalization ∙ ConeIso.rightIso cone-computation)

  opaque
    triangle-at : (x : Obj-abs Encoded.category) →
      (βv ∙ (pullback₂ {f = g} {p} ◁ (functor ∘ x))) =₂ βu
    triangle-at x = const-evaluate βu x ∙
      ((family-triangle ▷ x) ∙
        (isoComp-evaluate (const βv) (pullback₂ {f = g} {p} ◁ functor) x
          (const-evaluate βv x)
          (comp-assoc x functor (postWhisker (pullback₂ {f = g} {p})))) ⁻¹)

  action : Obj-abs Encoded.category → FunctorOverIso (lift-triangle first) (lift-triangle second)
  action x = record { underlying = functor ∘ x ; compatible = triangle-at x }

  comparison : FunctorOverIso u v → FunctorOverIso (lift-triangle first) (lift-triangle second)
  comparison Φ = action (Encoded.point Φ)

  congruence : {x y : Obj-abs Encoded.category} → x =₁ y →
    FunctorOverIso.underlying (action x) =₂ FunctorOverIso.underlying (action y)
  congruence δ = functor ◁ δ
```

The complete encoded input computation can be transported through base
change and evaluation. The conclusions below compare the underlying
resulting identifications. They do not assert a higher comparison of
the resulting native triangle witnesses. This statement uses the action
constructed above throughout.

```agda
  module LiftedFamily {A : CAT}
    (familyCone : Cone Encoded.leftMap Encoded.rightMap A)
    (universal : IsPullback familyCone) where
    module Family = Lift u v familyCone universal
      using (action; lift; encoded-computation)

    opaque
      base-change-image : (Φ : FunctorOverIso u v) →
        FunctorOverIso.underlying (comparison (Family.action (Family.lift Φ))) =₂
        FunctorOverIso.underlying (comparison Φ)
      base-change-image Φ = congruence (Family.encoded-computation Φ)

    evaluation-image : {E : CAT} (ε : MAP (Pullback g p) E) (Φ : FunctorOverIso u v) →
      (ε ◁ FunctorOverIso.underlying (comparison (Family.action (Family.lift Φ)))) =₂
      (ε ◁ FunctorOverIso.underlying (comparison Φ))
    evaluation-image ε Φ = postWhisker ε ◁ base-change-image Φ
```
