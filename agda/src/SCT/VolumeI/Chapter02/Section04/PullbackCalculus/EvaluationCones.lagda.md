# Evaluating an entire cone

Evaluation at an object of the diagram shape takes a cone of diagrams
to its evaluated cone. Uncurrying and restricting along that object give
the same cone, including the specified matching identification.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter02.Section04.PullbackCalculus.EvaluationCones
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointNaturality 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeUncurrying 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeUncurryingNormalization 𝒯 M ℱ using (endpoints-iterated)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯 using (coneIso-compose)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (cone-match-change)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯 using (transport-square)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.Cospans.ConeAction 𝒯 P using (module Action)
open import SCT.VolumeI.Chapter01.Section06.Coordinates.ProjectedCones 𝒯 using (module Coordinate)
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Postcomposition.PostcompositionParameterEvaluation as Post

module EvaluationCone {T C D E : CAT} (z : Obj-abs T) (f : MAP C E) (g : MAP D E) where
  cospan : CospanMap (funPost {C = T} f) (funPost g) f g
  cospan = record
    { left = evaluate z ; right = evaluate z ; base = evaluate z
    ; leftSquare = (evaluate-post z f) ⁻¹ ; rightSquare = (evaluate-post z g) ⁻¹ }
  module Induced = CospanMap cospan using (mapCone; pullbackMap; pullbackMap-β)
  module Act = Action cospan using (normalization; module Normal; map-iso; map-pre)
  module CoordinateEvaluation = Coordinate (funPost f) (funPost g) f g
    (evaluate z) (evaluate z) (evaluate z) (evaluate-post z f) (evaluate-post z g)
    using (read)

  normalized-evaluation : {Γ V : CAT} (F : MAP V E) (h : MAP Γ (Fun T V)) →
    (comp-assoc h (evaluate z) F ∙
      ((((evaluate-post z F) ⁻¹) ⁻¹ ▷ h) ∙ (comp-assoc h (funPost F) (evaluate z)) ⁻¹)) =₂
      evaluate-post-at z F h
  normalized-evaluation F h = isoComp-cong (idIso (comp-assoc h (evaluate z) F))
    (isoComp-cong (preWhisker h ◁ inverse-inverse (evaluate-post z F))
      (idIso ((comp-assoc h (funPost F) (evaluate z)) ⁻¹)))

  normalized-cone : {Γ : CAT} (s : Cone (funPost f) (funPost g) Γ) →
    ConeIso (Induced.mapCone s) (CoordinateEvaluation.read s)
  normalized-cone s = cone-match-change _ _ _ _
    (isoComp-cong (normalized-evaluation g (Cone.right s))
      (isoComp-cong (idIso (evaluate z ◁ Cone.match s))
        (＝-inv ◁ normalized-evaluation f (Cone.left s))) ∙ Act.normalization s)

  module At {Γ : CAT} (s : Cone (funPost f) (funPost g) Γ) where
    u = Cone.left s
    v = Cone.right s
    τ = Cone.match s
    i = insert {X = Γ} z
    af = comp-assoc i (funUncurry u) f
    ag = comp-assoc i (funUncurry v) g
    bf = funPost-uncurry f u ▷ i
    bg = funPost-uncurry g v ▷ i
    L = af ∙ bf
    R = ag ∙ bg
    δ = funUncurryIso τ ▷ i
    target : Cone f g Γ
    target = conePre i (uncurryCone s)

    target-normal : Cone.match target =₂ (R ∙ (δ ∙ L ⁻¹))
    target-normal = endpoints-iterated bf bg af ag δ ∙
      isoComp-cong (idIso ag)
        (isoComp-cong
          (isoComp-cong (idIso bg)
            (isoComp-cong (idIso δ) (pre-inverse (funPost-uncurry f u) i) ∙
              preWhisker-isoComp-at (funUncurryIso τ) ((funPost-uncurry f u) ⁻¹) i) ∙
            preWhisker-isoComp-at (funPost-uncurry g v)
              (funUncurryIso τ ∙ (funPost-uncurry f u) ⁻¹) i)
          (idIso (af ⁻¹)))

    evaluated : ConeIso (CoordinateEvaluation.read s) target
    evaluated = record
      { leftIso = evaluate-uncurry z u ; rightIso = evaluate-uncurry z v
      ; compatible = transport-square
          (evaluate-post-at z f u) L (evaluate-post-at z g v) R
          (evaluate z ◁ τ) δ
          (evaluate-uncurry z (funPost f ∘ u)) (evaluate-uncurry z (funPost g ∘ v))
          (f ◁ evaluate-uncurry z u) (g ◁ evaluate-uncurry z v)
          (Post.At.comparison 𝒯 M ℱ f u z ∙
            isoComp-assoc-at af bf (evaluate-uncurry z (funPost f ∘ u)))
          (Post.At.comparison 𝒯 M ℱ g v z ∙
            isoComp-assoc-at ag bg (evaluate-uncurry z (funPost g ∘ v)))
          ((Evaluation.natural z τ) ⁻¹) ∙
            isoComp-cong target-normal (idIso (f ◁ evaluate-uncurry z u)) }

    comparison : ConeIso (Induced.mapCone s) target
    comparison = coneIso-compose evaluated (normalized-cone s)
```
