# Corner comparisons in a family

The comparison of whole endpoint cones commutes with substitution of a
parameter. Its reversed form retains the inverse of the specified corner
identification. These are the two orientations needed for triangle vertices.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section02.EndpointCornerComparison as Corner

module SCT.VolumeI.Chapter02.Section02.EndpointCornerFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter02.Section02.RestrictionEvaluation 𝒯 M ℱ P
open import SCT.VolumeI.Chapter02.Section02.EndpointRestrictionCones 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section08.FunctorSquares 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section08.Squares 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeSymmetry 𝒯
open import SCT.VolumeI.Chapter01.Section06.InverseCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section04.CoherenceTransport 𝒯

abstract
  evaluate-cong-inverse : {A C : CAT} {x y : Obj-abs A} (α : x =₁ y) →
    (evaluate-cong {C = C} (α ⁻¹)) =₂ ((evaluate-cong α) ⁻¹)
  evaluate-cong-inverse {C = C} {x} α =
    (isoInverse-unique (evaluate-cong {C = C} α) (evaluate-cong (α ⁻¹))
      (evaluate-cong-id x ∙
        (evaluate-cong-Iso₂ (isoComp-inverseˡ-at α) ∙
          (evaluate-cong-comp (α ⁻¹) α) ⁻¹))) ⁻¹

  inverse-transport : {X Y : CAT} {a a′ b b′ : MAP X Y}
    (p : a =₁ a′) (q : b =₁ b′) (α : a =₁ b) →
    ((changeEndpoints p q α) ⁻¹) =₂ (changeEndpoints q p (α ⁻¹))
  inverse-transport p q α = isoComp-assoc-at p (α ⁻¹) (q ⁻¹) ∙
    (isoComp-cong (isoComp-cong (inverse-inverse p) (idIso (α ⁻¹))) (idIso (q ⁻¹)) ∙
    (isoComp-cong (inverse-composite α (p ⁻¹)) (idIso (q ⁻¹)) ∙
      inverse-composite q (α ∙ p ⁻¹)))

module At {A B D Γ C : CAT} {u : Obj-abs A} {v : Obj-abs B}
  {f : MAP A D} {g : MAP B D} (s : Square u v f g) (H : MAP Γ (Fun D C)) where
  open Endpoints C
  module Universal = Corner.At 𝒯 M ℱ P s C
  δ = Square.commute s
  p = evaluate-pre {C = C} f u
  q = evaluate-pre {C = C} g v
  vertex = evaluate-cong {C = C} δ
  left-assoc = comp-assoc H (funPre f) (evaluate u)
  right-assoc = comp-assoc H (funPre g) (evaluate v)
  original = convert (conePre H (functorOut s C))
  endpoint = conePre H Universal.endpoint-cone
  reversed-endpoint : Cone (evaluate {C = C} v) (evaluate u) (Fun D C)
  reversed-endpoint = record
    { left = funPre g ; right = funPre f
    ; match = p ⁻¹ ∙ (evaluate-cong (δ ⁻¹) ∙ q) }

  abstract
    matching : Cone.match original =₂ Cone.match endpoint
    matching = changeEndpoints-cong left-assoc right-assoc
      (preWhisker H ◁ Universal.matching) ∙
      Parameter.matching H (functorOut s C)

    reverse-universal : ((Cone.match Universal.endpoint-cone) ⁻¹) =₂
      Cone.match reversed-endpoint
    reverse-universal = isoComp-cong (idIso (p ⁻¹))
        (isoComp-cong ((evaluate-cong-inverse δ) ⁻¹) (idIso q)) ∙
      (isoComp-assoc-at (p ⁻¹) (vertex ⁻¹) q ∙
      (isoComp-cong (inverse-composite vertex p) (inverse-inverse q) ∙
        inverse-composite (q ⁻¹) (vertex ∙ p)))

    reversed-matching : Cone.match (coneSwap original) =₂
      Cone.match (conePre H reversed-endpoint)
    reversed-matching = changeEndpoints-cong right-assoc left-assoc
        ((preWhisker H ◁ reverse-universal) ∙
          (pre-inverse (Cone.match Universal.endpoint-cone) H) ⁻¹) ∙
      (inverse-transport left-assoc right-assoc (Cone.match Universal.endpoint-cone ▷ H) ∙
        (＝-inv ◁ matching))

  comparison : ConeIso original endpoint
  comparison = cone-match-change _ _ _ _ matching

  reversed-comparison : ConeIso (coneSwap original) (conePre H reversed-endpoint)
  reversed-comparison = cone-match-change _ _ _ _ reversed-matching
```
