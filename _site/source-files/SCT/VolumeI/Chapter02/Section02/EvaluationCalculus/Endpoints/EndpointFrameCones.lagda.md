# Corner cones specified by their vertex frames

A shape corner obtained from two maps to one vertex evaluates to the
quotient of the corresponding endpoint frames. This also holds after
substitution of a parameter category, with the specified associators.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Endpoints.TransposedEndpointFrames as Frames
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.FramedConeRestriction as Framed

module SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Endpoints.EndpointFrameCones
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionEvaluation 𝒯 M ℱ P public
open import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Endpoints.EndpointCornerFamilies 𝒯 M ℱ P using (evaluate-cong-inverse)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯 public
open import SCT.VolumeI.Chapter01.Section04.Substitution.CoherenceTransport 𝒯 using (changeEndpoints-cong)
open Frames.FrameCalculus 𝒯 M ℱ P using (quotient-pre)
open Framed 𝒯 M ℱ P using (framed-cone) public

frame : {Γ A B C : CAT} (d : MAP A B) (u : Obj-abs A)
  {z : Obj-abs B} (b : (d ∘ u) =₁ z) (W : MAP Γ (Fun B C)) →
  (evaluate u ∘ (funPre d ∘ W)) =₁ (evaluate z ∘ W)
frame d u b W = ((evaluate-cong b ∙ evaluate-pre d u) ▷ W) ∙
  (comp-assoc W (funPre d) (evaluate u)) ⁻¹

module At {Γ A D B C : CAT} (d : MAP A B) (k : MAP D B)
  (u : Obj-abs A) (v : Obj-abs D) {z : Obj-abs B}
  (b : (d ∘ u) =₁ z) (e : (k ∘ v) =₁ z) (W : MAP Γ (Fun B C)) where
  l = evaluate-cong {C = C} b
  r = evaluate-cong {C = C} e
  p = evaluate-pre {C = C} d u
  q = evaluate-pre {C = C} k v
  τ = q ⁻¹ ∙ (evaluate-cong (e ⁻¹ ∙ b) ∙ p)
  corner : Cone (evaluate {C = C} u) (evaluate v) (Fun B C)
  corner = record { left = funPre d ; right = funPre k ; match = τ }
  module Restricted = Framed.Restrict 𝒯 M ℱ P (funPre d) (funPre k) (l ∙ p) (r ∙ q) W

  abstract
    universal : τ =₂ ((r ∙ q) ⁻¹ ∙ (l ∙ p))
    universal = (quotient-pre l r p q) ⁻¹ ∙
      isoComp-cong (idIso (q ⁻¹))
        (isoComp-cong (isoComp-cong (evaluate-cong-inverse e) (idIso l) ∙
          evaluate-cong-comp (e ⁻¹) b) (idIso p))

    matching : Cone.match (conePre W corner) =₂
      (frame k v e W ⁻¹ ∙ frame d u b W)
    matching = Restricted.matching ∙
      changeEndpoints-cong (comp-assoc W (funPre d) (evaluate u))
        (comp-assoc W (funPre k) (evaluate v)) (preWhisker W ◁ universal)

-- Replace only the specified matchings, retaining both edge comparisons.
replace-matchings : {Γ A B C : CAT} {f : MAP A C} {g : MAP B C}
  {s t : Cone f g Γ} (Φ : ConeIso s t)
  (σ : (f ∘ Cone.left s) =₁ (g ∘ Cone.right s))
  (τ : (f ∘ Cone.left t) =₁ (g ∘ Cone.right t)) →
  Cone.match s =₂ σ → Cone.match t =₂ τ →
  ConeIso (record { left = Cone.left s ; right = Cone.right s ; match = σ })
    (record { left = Cone.left t ; right = Cone.right t ; match = τ })
replace-matchings {f = f} {g} Φ σ τ source target = record
  { leftIso = ConeIso.leftIso Φ ; rightIso = ConeIso.rightIso Φ
  ; compatible = isoComp-cong (idIso (g ◁ ConeIso.rightIso Φ)) source ∙
      ConeIso.compatible Φ ∙ isoComp-cong (target ⁻¹) (idIso (f ◁ ConeIso.leftIso Φ)) }
```
