# Postcomposition of a whole triangle corner

One calculation handles every pair of restricted edges. The edge
comparisons and the identification of their common vertex commute with
postcomposition, so reflection of the transported square retains the
specified matching.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.PostcompositionCorners
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section02.PostcompositionEndpointCones 𝒯 M ℱ I public
import SCT.VolumeI.Chapter02.Section02.EndpointConeRoutes as Routes
import SCT.VolumeI.Chapter02.Section02.PostcompositionRestrictionEvaluation as Edges
import SCT.VolumeI.Chapter02.Section02.PostcompositionObjectEvaluation as Objects
open import SCT.VolumeI.Chapter01.Section06.ComparisonSquares 𝒯 using (reflect-transport-square)
open import SCT.VolumeI.Chapter01.Section04.CoherenceTransport 𝒯
  using (changeEndpoints; square-to-changeEndpoints)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

module At {Γ B C D : CAT} (F : MAP C D) (u v : Obj-abs [1]) (d k : MAP [1] B)
  (δ : (d ∘ u) =₁ (k ∘ v)) (h : MAP Γ (Fun B C)) where
  hF = funPost F ∘ h
  module Before = Routes.At 𝒯 M ℱ I u v d k δ h
  module After = Routes.At 𝒯 M ℱ I u v d k δ hF
  module Left = Edges.At 𝒯 M ℱ P I E F d h
  module Right = Edges.At 𝒯 M ℱ P I E F k h
  output = post-cone F u v Before.family
  Kl = evaluate-post-at u F (funPre d ∘ h)
  Kr = evaluate-post-at v F (funPre k ∘ h)
  L = (F ◁ Before.left-route) ∙ Kl
  R = (F ◁ Before.right-route) ∙ Kr
  vertex = F ◁ (Before.vertex ▷ h)
  α = evaluate-post-at (d ∘ u) F h
  β = evaluate-post-at (k ∘ v) F h
  left-image = evaluate u ◁ Left.edge-comparison
  right-image = evaluate v ◁ Right.edge-comparison
  τ = F ◁ Before.matching

  abstract
    clear-frames : (R ∙ Cone.match output) =₂ (vertex ∙ L)
    clear-frames = isoComp-assoc-at vertex (F ◁ Before.left-route) Kl ∙
      isoComp-cong
        (postWhisker-isoComp-at F (Before.vertex ▷ h) Before.left-route ∙
          (postWhisker F ◁ Before.clear-frames) ∙
          (postWhisker-isoComp-at F Before.right-route Before.matching) ⁻¹) (idIso Kl) ∙
      (isoComp-assoc-at (F ◁ Before.right-route) τ Kl) ⁻¹ ∙
      isoComp-cong (idIso (F ◁ Before.right-route)) (cancel-inverse Kr (τ ∙ Kl)) ∙
      isoComp-assoc-at (F ◁ Before.right-route) Kr (Cone.match output)

    normalized : changeEndpoints L R (Cone.match output) =₂ vertex
    normalized = square-to-changeEndpoints L R (Cone.match output) vertex clear-frames

    left-square : (L ∙ left-image) =₂ (α ∙ After.left-route)
    left-square = Left.Endpoint.comparison u ∙ isoComp-assoc-at (F ◁ Before.left-route) Kl left-image

    right-square : (R ∙ right-image) =₂ (β ∙ After.right-route)
    right-square = Right.Endpoint.comparison v ∙ isoComp-assoc-at (F ◁ Before.right-route) Kr right-image

    compatible : (Cone.match output ∙ left-image) =₂ (right-image ∙ After.matching)
    compatible = reflect-transport-square After.left-route L After.right-route R
      After.matching (Cone.match output) left-image right-image α β left-square right-square
      (isoComp-cong (idIso β) (After.normalized ⁻¹) ∙
        (Objects.At.comparison 𝒯 M ℱ F h δ) ⁻¹ ∙
        isoComp-cong normalized (idIso α))

  comparison : ConeIso After.family output
  comparison = record
    { leftIso = Left.edge-comparison ; rightIso = Right.edge-comparison
    ; compatible = compatible }

open import SCT.VolumeI.Chapter01.Section06.ConeCalculus 𝒯 using (coneIso-compose; coneIso-adjust)

module FramedComparison {Γ B C D : CAT} (F : MAP C D)
  (u v : Obj-abs [1]) (d k : MAP [1] B) (δ : (d ∘ u) =₁ (k ∘ v))
  (h : MAP Γ (Fun B C)) (f g : MAP Γ (Ar C)) {x : MAP Γ C}
  (p : (evaluate u ∘ f) =₁ x) (q : (evaluate v ∘ g) =₁ x)
  (Φ : ConeIso (Routes.At.family 𝒯 M ℱ I u v d k δ h) (Framed.original F u v f g p q)) where
  module Corner = At F u v d k δ h
  module Frames = Framed F u v f g p q
  left-edge = (funPost F ◁ ConeIso.leftIso Φ) ∙ Corner.Left.edge-comparison
  right-edge = (funPost F ◁ ConeIso.rightIso Φ) ∙ Corner.Right.edge-comparison
  raw = coneIso-compose Frames.comparison
    (coneIso-compose (post-coneIso F u v Φ) Corner.comparison)

  comparison : ConeIso Corner.After.family Frames.reframed
  comparison = coneIso-adjust raw left-edge right-edge
    (isoComp-unitˡ-at left-edge) (isoComp-unitˡ-at right-edge)
```
