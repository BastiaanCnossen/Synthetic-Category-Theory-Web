# Postcomposition of an explicitly curried diagram

The comparison commutes with evaluation at each endpoint and uses the
original curry beta witness. Thus applying a functor to a morphism
expression agrees with currying the postcomposed diagram, including
the two displayed endpoint identifications.

For squares, the functor can itself be evaluation at an interval endpoint.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Postcomposition.CurryPostcomposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IsomorphismLifting 𝒯 M ℱ
open import SCT.VolumeI.Chapter02.Section02.UnitCalculus.DirectUnitTriangles 𝒯 M ℱ P I E using (module ReflectedEndpoint)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I using (post-boundary-normal)
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Postcomposition.PostcompositionParameterEvaluation as Post
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
open Structural vocabulary terminal products productLaws composition whiskering using (whisker-mixed-at)

module Evaluation {Γ A C D : CAT} (F : MAP C D) (H : MAP (Γ × A) C) (v : Obj-abs A) where
  h = funCurry H
  β = funCurry-β H
  φ = funPost-uncurry F h
  i = insert {X = Γ} v
  Q = evaluate-uncurry v (funPost F ∘ h)
  original = evaluate-uncurry v h
  output = evaluate-post-at v F h
  before = comp-assoc i (funUncurry h) F
  after = comp-assoc i H F
  raw = (F ◁ β) ∙ φ
  b = (F ◁ β) ▷ i
  f = φ ▷ i
  image = F ◁ (β ▷ i)

  abstract
    comparison : (after ∙ ((raw ▷ i) ∙ Q)) =₂ ((F ◁ evaluate-curry v H) ∙ output)
    comparison =
      isoComp-cong ((postWhisker-isoComp-at F (β ▷ i) original) ⁻¹) (idIso output) ∙
      (isoComp-assoc-at image (F ◁ original) output) ⁻¹ ∙
      isoComp-cong (idIso image) (Post.At.comparison 𝒯 M ℱ F h v) ∙
      isoComp-assoc-at image before (f ∙ Q) ∙
      isoComp-cong (whisker-mixed-at β i F) (idIso (f ∙ Q)) ∙
      (isoComp-assoc-at after b (f ∙ Q)) ⁻¹ ∙
      isoComp-cong (idIso after) (isoComp-assoc-at b f Q) ∙
      isoComp-cong (idIso after)
        (isoComp-cong (preWhisker-isoComp-at (F ◁ β) φ i) (idIso Q))

module At {Γ C D : CAT} (F : MAP C D) {x y : MAP Γ C}
  (H : MAP (Γ × [1]) C) (p : (H ∘ insert zero) =₁ x) (q : (H ∘ insert one) =₁ y) where
  original = expression H p q
  postcomposed = post-expression F original
  result = expression (F ∘ H)
    ((F ◁ p) ∙ comp-assoc (insert zero) H F)
    ((F ◁ q) ∙ comp-assoc (insert one) H F)
  h = funCurry H
  source-arrow = funPost F ∘ h
  target-arrow = funCurry (F ∘ H)
  β = funCurry-β (F ∘ H)
  raw = (F ◁ funCurry-β H) ∙ funPost-uncurry F h
  δ = funIsoReflect source-arrow target-arrow (β ⁻¹ ∙ raw)

  module Endpoint (v : Obj-abs [1]) {z : MAP Γ C} (r : (H ∘ insert v) =₁ z) where
    i = insert {X = Γ} v
    frame = r ∙ evaluate-curry v H
    front = F ◁ r
    aH = comp-assoc i H F
    Q = evaluate-curry v (F ∘ H)
    post = evaluate-post-at v F h
    module Reflected = ReflectedEndpoint v source-arrow target-arrow β raw δ
      (funIsoReflect-β source-arrow target-arrow (β ⁻¹ ∙ raw))
      using (endpoint)

    abstract
      compatible : (((front ∙ aH) ∙ Q) ∙ (evaluate v ◁ δ)) =₂ post-boundary v F h frame
      compatible = (post-boundary-normal v F h frame) ⁻¹ ∙
        isoComp-cong ((postWhisker-isoComp-at F r (evaluate-curry v H)) ⁻¹) (idIso post) ∙
        (isoComp-assoc-at front (F ◁ evaluate-curry v H) post) ⁻¹ ∙
        isoComp-cong (idIso front) (Evaluation.comparison F H v) ∙
        isoComp-assoc-at front aH ((raw ▷ i) ∙ evaluate-uncurry v source-arrow) ∙
        isoComp-cong (idIso (front ∙ aH)) Reflected.endpoint ∙
        isoComp-assoc-at (front ∙ aH) Q (evaluate v ◁ δ)

  comparison : ExpressionIso postcomposed result
  comparison = record
    { comparison = δ
    ; source-compatible = Endpoint.compatible zero p
    ; target-compatible = Endpoint.compatible one q }
```
