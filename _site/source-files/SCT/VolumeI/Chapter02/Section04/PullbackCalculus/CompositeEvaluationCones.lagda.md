# Evaluating composite functors as entire cones

The evaluation square of a composite compares with the evaluation square
of its second factor after expanding the first factor. The first leg is
the inverse evaluation frame. This specified leg is needed when pasting
the Segal square with an endpoint square.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter02.Section04.PullbackCalculus.CompositeEvaluationCones
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CompositeCones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯
  using (coneSwap; coneSwap-pre; coneIso-swap)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯
  using (inverse-composite; inverse-inverse; inverse-identity; pre-inverse)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.EvaluationComposition as Composition

module At {T A B C : CAT} (v : Obj-abs T) (f : MAP A B) (g : MAP B C) where
  module Compare = Composition.Composite 𝒯 M ℱ {T = T} f g using (comparison; module At)
  module Endpoint = Compare.At v using (endpoint)

  square : {X Y : CAT} (h : MAP X Y) → Cone (evaluate {C = Y} v) h (Fun T X)
  square h = record { left = funPost h ; right = evaluate v ; match = evaluate-post v h }

  d = evaluate-post v f
  n = evaluate-post-at v g (funPost f)
  m₀ = evaluate-post v (g ∘ f)
  z = evaluate v ◁ Compare.comparison
  a₀ = comp-assoc (evaluate v) f g

  abstract
    matching : (n ⁻¹ ∙ (g ◁ d ⁻¹)) =₂
      ((evaluate v ◁ Compare.comparison ⁻¹) ∙ (m₀ ⁻¹ ∙ a₀ ⁻¹))
    matching =
      isoComp-cong ((post-inverse (evaluate v) Compare.comparison) ⁻¹)
        (idIso (m₀ ⁻¹ ∙ a₀ ⁻¹)) ∙
      (isoComp-assoc-at (z ⁻¹) (m₀ ⁻¹) (a₀ ⁻¹) ∙
      (isoComp-cong (inverse-composite m₀ z) (idIso (a₀ ⁻¹)) ∙
      (inverse-composite a₀ (m₀ ∙ z) ∙
      ((＝-inv ◁ Endpoint.endpoint ⁻¹) ∙
      ((inverse-composite (g ◁ d) n) ⁻¹ ∙
        isoComp-cong (idIso (n ⁻¹)) (post-inverse g d))))))

  comparison : ConeIso (compositeCone f g (coneSwap (square (g ∘ f))))
    (coneSwap (conePre (funPost f) (square g)))
  comparison = record { leftIso = d ⁻¹ ; rightIso = Compare.comparison ⁻¹ ; compatible = matching }

  module Restrict {Γ : CAT} (F : MAP Γ (Fun T A)) where
    raw : ConeIso (compositeCone f g (coneSwap (conePre F (square (g ∘ f)))))
      (coneSwap (conePre (funPost f ∘ F) (square g)))
    raw = coneIso-compose (coneIso-swap (conePre-assoc F (funPost f) (square g)))
      (coneIso-compose (coneSwap-pre F (conePre (funPost f) (square g)))
      (coneIso-compose (coneIso-pre F comparison)
      (coneIso-compose (coneIso-inverse (compositeCone-pre f g F (coneSwap (square (g ∘ f)))))
        (compositeConeIso f g (coneIso-inverse (coneSwap-pre F (square (g ∘ f))))))))

    abstract
      left-frame : ConeIso.leftIso raw =₂ (evaluate-post-at v f F) ⁻¹
      left-frame = inverse-frame ∙ isoComp-cong (idIso b₁)
        (isoComp-cong (idIso d₁) tail-normal ∙ isoComp-unitˡ-at (d₁ ∙ tail))
        where
        a₁ : ((f ∘ evaluate v) ∘ F) =₁ (f ∘ (evaluate v ∘ F))
        a₁ = comp-assoc F (evaluate v) f
        b₁ : ((evaluate v ∘ funPost f) ∘ F) =₁ (evaluate v ∘ (funPost f ∘ F))
        b₁ = comp-assoc F (funPost f) (evaluate v)
        d₁ : ((f ∘ evaluate v) ∘ F) =₁ ((evaluate v ∘ funPost f) ∘ F)
        d₁ = d ⁻¹ ▷ F
        tail : (f ∘ (evaluate v ∘ F)) =₁ ((f ∘ evaluate v) ∘ F)
        tail = a₁ ⁻¹ ∙ (f ◁ (idIso (evaluate v ∘ F)) ⁻¹)
        tail-normal : tail =₂ a₁ ⁻¹
        tail-normal = isoComp-unitʳ-at (a₁ ⁻¹) ∙
          isoComp-cong (idIso (a₁ ⁻¹))
            (postWhisker-idIso f (evaluate v ∘ F) ∙
              (postWhisker f ◁ inverse-identity (evaluate v ∘ F)))
        inverse-frame : (b₁ ∙ (d₁ ∙ a₁ ⁻¹)) =₂ (evaluate-post-at v f F) ⁻¹
        inverse-frame = (inverse-composite a₁ ((d ▷ F) ∙ b₁ ⁻¹)) ⁻¹ ∙
          isoComp-cong ((inverse-composite (d ▷ F) (b₁ ⁻¹)) ⁻¹) (idIso (a₁ ⁻¹)) ∙
          (isoComp-assoc-at ((b₁ ⁻¹) ⁻¹) ((d ▷ F) ⁻¹) (a₁ ⁻¹)) ⁻¹ ∙
          isoComp-cong ((inverse-inverse b₁) ⁻¹)
            (isoComp-cong (pre-inverse d F) (idIso (a₁ ⁻¹)))

    framed-comparison : ConeIso (compositeCone f g (coneSwap (conePre F (square (g ∘ f)))))
      (coneSwap (conePre (funPost f ∘ F) (square g)))
    framed-comparison = coneIso-adjust raw ((evaluate-post-at v f F) ⁻¹)
      (ConeIso.rightIso raw) left-frame (idIso _)
```
