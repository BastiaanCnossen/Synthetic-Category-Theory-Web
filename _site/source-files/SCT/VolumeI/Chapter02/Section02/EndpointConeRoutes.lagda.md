# The two routes through a parametrized corner

Removing the two edge-evaluation frames from a restricted endpoint cone
leaves exactly the specified identification of the two vertex functors.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.EndpointConeRoutes
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯 public
open import SCT.VolumeI.Chapter01.Section06.InverseCalculus 𝒯 using (pre-inverse)
open import SCT.VolumeI.Chapter01.Section04.CoherenceTransport 𝒯
  using (changeEndpoints; square-to-changeEndpoints)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left)

module At {Γ B C : CAT} (u v : Obj-abs [1]) (d k : MAP [1] B)
  (δ : (d ∘ u) =₁ (k ∘ v)) (h : MAP Γ (Fun B C)) where
  p = evaluate-pre {C = C} d u
  q = evaluate-pre {C = C} k v
  vertex = evaluate-cong {C = C} δ
  aL = comp-assoc h (funPre d) (evaluate u)
  aR = comp-assoc h (funPre k) (evaluate v)
  left-route = (p ▷ h) ∙ aL ⁻¹
  right-route = (q ▷ h) ∙ aR ⁻¹
  τ = q ⁻¹ ∙ (vertex ∙ p)
  cone : Cone (evaluate {C = C} u) (evaluate v) (Fun B C)
  cone = record { left = funPre d ; right = funPre k ; match = τ }
  family = conePre h cone
  matching = Cone.match family

  abstract
    matching-image : (τ ▷ h) =₂ ((q ▷ h) ⁻¹ ∙ ((vertex ▷ h) ∙ (p ▷ h)))
    matching-image = isoComp-cong (pre-inverse q h) (preWhisker-isoComp-at vertex p h) ∙
      preWhisker-isoComp-at (q ⁻¹) (vertex ∙ p) h

    clear-frames : (right-route ∙ matching) =₂ ((vertex ▷ h) ∙ left-route)
    clear-frames = isoComp-assoc-at (vertex ▷ h) (p ▷ h) (aL ⁻¹) ∙
      isoComp-cong (cancel-inverse (q ▷ h) ((vertex ▷ h) ∙ (p ▷ h))) (idIso (aL ⁻¹)) ∙
      (isoComp-assoc-at (q ▷ h) ((q ▷ h) ⁻¹ ∙ ((vertex ▷ h) ∙ (p ▷ h))) (aL ⁻¹)) ⁻¹ ∙
      isoComp-cong (idIso (q ▷ h)) (isoComp-cong matching-image (idIso (aL ⁻¹))) ∙
      isoComp-cong (idIso (q ▷ h)) (cancel-left aR ((τ ▷ h) ∙ aL ⁻¹)) ∙
      isoComp-assoc-at (q ▷ h) (aR ⁻¹) matching

    normalized : changeEndpoints left-route right-route matching =₂ (vertex ▷ h)
    normalized = square-to-changeEndpoints left-route right-route matching (vertex ▷ h) clear-frames
```
