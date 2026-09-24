# Postcomposition of whole endpoint cones

Postcomposition transports the matching identification through its two
evaluation comparisons. It acts on comparisons of cones and agrees with
the literal endpoint frames of postcomposed morphism expressions.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.PostcompositionEndpointCones
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.ExpressionPostcomposition 𝒯 M ℱ I
  using (post-evaluation-natural; post-boundary-normal)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯 public
open import SCT.VolumeI.Chapter01.Section06.ConeSymmetry 𝒯 using (cone-match-change)
open import SCT.VolumeI.Chapter01.Section06.ComparisonSquares 𝒯 using (post-square)
open import SCT.VolumeI.Chapter01.Section04.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section06.InverseCalculus 𝒯 using (inverse-composite; inverse-inverse)
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

post-cone : {Γ C D : CAT} (F : MAP C D) (u v : Obj-abs [1]) →
  Cone (evaluate {C = C} u) (evaluate v) Γ → Cone (evaluate {C = D} u) (evaluate v) Γ
post-cone F u v s = record
  { left = funPost F ∘ Cone.left s
  ; right = funPost F ∘ Cone.right s
  ; match = (evaluate-post-at v F (Cone.right s)) ⁻¹ ∙
      ((F ◁ Cone.match s) ∙ evaluate-post-at u F (Cone.left s)) }

post-coneIso : {Γ C D : CAT} (F : MAP C D) (u v : Obj-abs [1])
  {s t : Cone (evaluate {C = C} u) (evaluate v) Γ} → ConeIso s t →
  ConeIso (post-cone F u v s) (post-cone F u v t)
post-coneIso F u v {s} {t} Φ = record
  { leftIso = funPost F ◁ ConeIso.leftIso Φ
  ; rightIso = funPost F ◁ ConeIso.rightIso Φ
  ; compatible = isoComp-cong (idIso β) (isoComp-assoc-at (Rs ⁻¹) τs Ls) ∙
      paste-squares Ls Lt ((Rs ⁻¹) ∙ τs) ((Rt ⁻¹) ∙ τt) α imageLeft β
        (post-evaluation-natural u F (ConeIso.leftIso Φ))
        (paste-squares τs τt (Rs ⁻¹) (Rt ⁻¹) imageLeft imageRight β
          (post-square F _ _ _ _ (ConeIso.compatible Φ))
          (move-square Rt β imageRight Rs (post-evaluation-natural v F (ConeIso.rightIso Φ)))) ∙
      isoComp-cong ((isoComp-assoc-at (Rt ⁻¹) τt Lt) ⁻¹) (idIso α) }
  where
  Ls = evaluate-post-at u F (Cone.left s)
  Lt = evaluate-post-at u F (Cone.left t)
  Rs = evaluate-post-at v F (Cone.right s)
  Rt = evaluate-post-at v F (Cone.right t)
  τs = F ◁ Cone.match s
  τt = F ◁ Cone.match t
  α = evaluate u ◁ (funPost F ◁ ConeIso.leftIso Φ)
  β = evaluate v ◁ (funPost F ◁ ConeIso.rightIso Φ)
  imageLeft = F ◁ (evaluate u ◁ ConeIso.leftIso Φ)
  imageRight = F ◁ (evaluate v ◁ ConeIso.rightIso Φ)

module Framed {Γ C D : CAT} (F : MAP C D) (u v : Obj-abs [1])
  (f g : MAP Γ (Ar C)) {x : MAP Γ C}
  (p : (evaluate u ∘ f) =₁ x) (q : (evaluate v ∘ g) =₁ x) where
  original : Cone (evaluate u) (evaluate v) Γ
  original = record { left = f ; right = g ; match = q ⁻¹ ∙ p }
  reframed : Cone (evaluate {C = D} u) (evaluate v) Γ
  reframed = record
    { left = funPost F ∘ f ; right = funPost F ∘ g
    ; match = (post-boundary v F g q) ⁻¹ ∙ post-boundary u F f p }
  L = evaluate-post-at u F f
  R = evaluate-post-at v F g

  abstract
    matching : Cone.match (post-cone F u v original) =₂ Cone.match reframed
    matching = isoComp-cong (＝-inv ◁ (post-boundary-normal v F g q) ⁻¹)
        ((post-boundary-normal u F f p) ⁻¹) ∙
      isoComp-cong ((inverse-composite (F ◁ q) R) ⁻¹) (idIso ((F ◁ p) ∙ L)) ∙
      (isoComp-assoc-at (R ⁻¹) ((F ◁ q) ⁻¹) ((F ◁ p) ∙ L)) ⁻¹ ∙
      isoComp-cong (idIso (R ⁻¹)) (isoComp-assoc-at ((F ◁ q) ⁻¹) (F ◁ p) L) ∙
      isoComp-cong (idIso (R ⁻¹))
        (isoComp-cong (isoComp-cong (post-inverse F q) (idIso (F ◁ p)) ∙
          postWhisker-isoComp-at F (q ⁻¹) p) (idIso L))

  comparison : ConeIso (post-cone F u v original) reframed
  comparison = cone-match-change _ _ _ _ matching
```
