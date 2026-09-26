# Transporting a framed corner through restriction

The restriction routes of two edges carry their specified common vertex.
A shape-level corner equation therefore gives an endpoint equation for
their evaluated families. The final cancellation removes only the common
specified frame.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Endpoints.EndpointInputNaturality as Inputs
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionCornerTransport
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionEvaluation 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left)

module At {A B D K C : CAT} (u : Obj-abs A) (v : Obj-abs B)
  (d : MAP A K) (k : MAP B K) (s : MAP K D) (δ : (d ∘ u) =₁ (k ∘ v)) where
  X = Fun D C
  R = funPre {D = C} s
  p = evaluate-pre {C = C} d u
  q = evaluate-pre {C = C} k v
  middle = evaluate-cong {C = C} δ
  aL = comp-assoc R (funPre d) (evaluate u)
  aR = comp-assoc R (funPre k) (evaluate v)
  l = (p ▷ R) ∙ aL ⁻¹
  r = (q ▷ R) ∙ aR ⁻¹
  τ = q ⁻¹ ∙ (middle ∙ p)
  cone : Cone (evaluate {C = C} u) (evaluate v) (Fun K C)
  cone = record { left = funPre d ; right = funPre k ; match = τ }
  matching = Cone.match (conePre R cone)
  left-prefix = evaluate-pre {C = C} s (d ∘ u)
  right-prefix = evaluate-pre {C = C} s (k ∘ v)
  left-route = left-prefix ∙ l
  right-route = right-prefix ∙ r
  vertex = evaluate-cong {C = C} (s ◁ δ)

  abstract
    matching-image : (τ ▷ R) =₂ ((q ▷ R) ⁻¹ ∙ ((middle ▷ R) ∙ (p ▷ R)))
    matching-image = isoComp-cong (pre-inverse q R) (preWhisker-isoComp-at middle p R) ∙
      preWhisker-isoComp-at (q ⁻¹) (middle ∙ p) R

    clear-frames : (r ∙ matching) =₂ ((middle ▷ R) ∙ l)
    clear-frames = isoComp-assoc-at (middle ▷ R) (p ▷ R) (aL ⁻¹) ∙
      (isoComp-cong (cancel-inverse (q ▷ R) ((middle ▷ R) ∙ (p ▷ R))) (idIso (aL ⁻¹)) ∙
      ((isoComp-assoc-at (q ▷ R) ((q ▷ R) ⁻¹ ∙ ((middle ▷ R) ∙ (p ▷ R))) (aL ⁻¹)) ⁻¹ ∙
      (isoComp-cong (idIso (q ▷ R)) (isoComp-cong matching-image (idIso (aL ⁻¹))) ∙
      (isoComp-cong (idIso (q ▷ R)) (cancel-left aR ((τ ▷ R) ∙ aL ⁻¹)) ∙
        isoComp-assoc-at (q ▷ R) (aR ⁻¹) matching))))

    comparison : (right-route ∙ matching) =₂ (vertex ∙ left-route)
    comparison = isoComp-assoc-at vertex left-prefix l ∙
      (isoComp-cong (Inputs.RestrictionObject.natural 𝒯 M ℱ {C = C} s δ) (idIso l) ∙
      ((isoComp-assoc-at right-prefix (middle ▷ R) l) ⁻¹ ∙
      (isoComp-cong (idIso right-prefix) clear-frames ∙
        isoComp-assoc-at right-prefix r matching)))

  module Framed {z : Obj-abs D}
    (θL : (s ∘ (d ∘ u)) =₁ z) (θR : (s ∘ (k ∘ v)) =₁ z)
    (shape : θL =₂ (θR ∙ (s ◁ δ)))
    {a b : MAP X C} (nl : a =₁ evaluate {C = C} z) (nr : b =₁ evaluate z)
    (L : (evaluate u ∘ (funPre d ∘ R)) =₁ a)
    (R′ : (evaluate v ∘ (funPre k ∘ R)) =₁ b)
    (left-image : (nl ∙ L) =₂ (evaluate-cong θL ∙ left-route))
    (right-image : (nr ∙ R′) =₂ (evaluate-cong θR ∙ right-route)) where

    abstract
      framed : (nl ∙ L) =₂ ((nr ∙ R′) ∙ matching)
      framed = isoComp-cong (right-image ⁻¹) (idIso matching) ∙
        ((isoComp-assoc-at (evaluate-cong θR) right-route matching) ⁻¹ ∙
        (isoComp-cong (idIso (evaluate-cong θR)) (comparison ⁻¹) ∙
        (isoComp-assoc-at (evaluate-cong θR) vertex left-route ∙
        (isoComp-cong (evaluate-cong-comp θR (s ◁ δ) ∙ evaluate-cong-Iso₂ shape)
          (idIso left-route) ∙ left-image))))

      vertex-equation : ((nr ⁻¹ ∙ nl) ∙ L) =₂ (R′ ∙ matching)
      vertex-equation = cancel-left nr (R′ ∙ matching) ∙
        (isoComp-cong (idIso (nr ⁻¹)) (isoComp-assoc-at nr R′ matching ∙ framed) ∙
          isoComp-assoc-at (nr ⁻¹) nl L)
```
