# Identity expressions under an endpoint identification

An identification of objects identifies their identity expressions.
The same identification changes both endpoint frames.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.IdentityExpressionRetargeting
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section02.DirectUnitTriangles 𝒯 M ℱ P I E
  using (module ReflectedEndpoint)
open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter01.Section07.IsomorphismLifting 𝒯 M ℱ
  using (funIsoReflect; funIsoReflect-β)
open import SCT.VolumeI.Chapter01.Section04.SplitProjectionNaturality 𝒯 M using (section-natural)

module At {Γ C : CAT} {x y : MAP Γ C} (p : x =₁ y) where
  H = x ∘ pr₁ {C = Γ} {D = [1]}
  K = y ∘ pr₁ {C = Γ} {D = [1]}
  F = funCurry H
  G = funCurry K
  β = funCurry-β H
  θ = (p ▷ pr₁) ∙ β
  raw = (funCurry-β K) ⁻¹ ∙ θ
  δ = funIsoReflect F G raw

  module Endpoint (z : Obj-abs [1]) where
    i = insert {X = Γ} z
    b = identity-boundary z x
    b′ = identity-boundary z y
    u = (p ▷ pr₁) ▷ i
    v = β ▷ i
    Q = evaluate-uncurry z F
    module Reflected = ReflectedEndpoint z F G (funCurry-β K) θ δ (funIsoReflect-β F G raw)

    abstract
      normalized : (b′ ∙ ((θ ▷ i) ∙ Q)) =₂ (p ∙ (b ∙ evaluate-curry z H))
      normalized = isoComp-assoc-at p b (evaluate-curry z H) ∙
        isoComp-cong (section-natural pr₁ i (pair-β₁ _ _) p) (idIso (v ∙ Q)) ∙
        (isoComp-assoc-at b′ u (v ∙ Q)) ⁻¹ ∙
        isoComp-cong (idIso b′) (isoComp-assoc-at u v Q) ∙
        isoComp-cong (idIso b′) (isoComp-cong (preWhisker-isoComp-at (p ▷ pr₁) β i) (idIso Q))

      comparison : ((b′ ∙ evaluate-curry z K) ∙ (evaluate z ◁ δ)) =₂
        (p ∙ (b ∙ evaluate-curry z H))
      comparison = normalized ∙ isoComp-cong (idIso b′) Reflected.endpoint ∙
        isoComp-assoc-at b′ (evaluate-curry z K) (evaluate z ◁ δ)

  comparison : ExpressionIso (retarget-expression (identity-expression x) p p) (identity-expression y)
  comparison = record
    { comparison = δ
    ; source-compatible = Endpoint.comparison zero
    ; target-compatible = Endpoint.comparison one }
```
