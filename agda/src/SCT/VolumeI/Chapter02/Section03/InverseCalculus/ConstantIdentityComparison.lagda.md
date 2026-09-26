# Constant arrows and identity expressions

The constant-arrow functor applied to a term agrees with its identity
expression, with both specified endpoint frames. The first projection
of the insertion square supplies the compatibility needed by currying.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section03.InverseCalculus.ConstantIdentityComparison
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section02.UnitCalculus.DirectUnitTriangles 𝒯 M ℱ P I E
  using (module ReflectedEndpoint)
open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IsomorphismLifting 𝒯 M ℱ
  using (funIsoReflect; funIsoReflect-β)
open import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.InsertionEvaluation 𝒯 M ℱ
  using (evaluate-insertion; evaluate-uncurry-compose)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.SquareEvaluation 𝒯 M using (change-evaluation)
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.ConstantArrows 𝒯 M ℱ I using (constant-frame; constant-identification)
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity 𝒯 M using (cancel-inverse-tail)
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.InsertionProjectionWitnesses as Insertion

module At {Γ C : CAT} (r : MAP Γ C) where
  H = pr₁ {C = C} {D = [1]}
  K = r ∘ pr₁ {C = Γ} {D = [1]}
  F = identityArrow {C}
  G = funCurry K
  R = productMap r (id [1])
  bR = pair-β₁ (r ∘ pr₁) (id [1] ∘ pr₂)
  D = bR
  β = funCurry-β H
  U = funUncurry-restrict F r
  θ = D ∙ ((β ▷ R) ∙ U)
  raw = (funCurry-β K) ⁻¹ ∙ θ
  δ = funIsoReflect (F ∘ r) G raw

  module Endpoint (z : Obj-abs [1]) where
    i = insert {X = Γ} z
    j = insert {X = C} z
    module Projection = Insertion.Parameter 𝒯 M ℱ r z
    module Reflected = ReflectedEndpoint z (F ∘ r) G (funCurry-β K) θ δ
      (funIsoReflect-β (F ∘ r) G raw)
    Q = evaluate-uncurry z F
    Qr = evaluate-uncurry z (F ∘ r)
    A = (comp-assoc r F (evaluate z)) ⁻¹
    e = evaluate-insertion (funUncurry F) r z
    eH = evaluate-insertion H r z
    b = pair-β₁ (id C) (const z)
    b′ = identity-boundary z r
    d = D ▷ i
    v = (β ▷ R) ▷ i
    w = (β ▷ j) ▷ r

    T = comp-assoc i R pr₁
    V = comp-assoc r j pr₁
    image = pr₁ ◁ insert-natural r z
    u = comp-unitˡ r
    jβ = b ▷ r

    abstract
      projection : ((b′ ∙ d) ∙ eH) =₂ (u ∙ jβ)
      projection = isoComp-cong (idIso u) (cancel-inverse-tail jβ V) ∙
        isoComp-assoc-at u (jβ ∙ V ⁻¹) V ∙
        isoComp-cong Projection.projection₁ (idIso V) ∙
        (isoComp-assoc-at (b′ ∙ (d ∙ T ⁻¹)) image V) ⁻¹ ∙
        isoComp-cong (idIso (b′ ∙ (d ∙ T ⁻¹))) (idIso (image ∙ V)) ∙
        isoComp-cong (isoComp-assoc-at b′ d (T ⁻¹)) (idIso (image ∙ V)) ∙
        (isoComp-assoc-at (b′ ∙ d) (T ⁻¹) (image ∙ V)) ⁻¹

      raw-image : ((θ ▷ i) ∙ Qr) =₂
        (d ∙ ((v ∙ e) ∙ ((Q ▷ r) ∙ A)))
      raw-image = isoComp-cong (idIso d)
          ((isoComp-assoc-at v e ((Q ▷ r) ∙ A)) ⁻¹ ∙
          (isoComp-cong (idIso v)
            (isoComp-assoc-at e (Q ▷ r) A ∙ evaluate-uncurry-compose z F r) ∙
          (isoComp-assoc-at v (U ▷ i) Qr ∙
            isoComp-cong (preWhisker-isoComp-at (β ▷ R) U i) (idIso Qr)))) ∙
        (isoComp-assoc-at d (((β ▷ R) ∙ U) ▷ i) Qr ∙
          isoComp-cong (preWhisker-isoComp-at D ((β ▷ R) ∙ U) i) (idIso Qr))

      changed-evaluation : (v ∙ e) =₂ (eH ∙ w)
      changed-evaluation = (change-evaluation β r R i j (insert-natural r z)) ⁻¹

      regroup : (b′ ∙ (d ∙ ((eH ∙ w) ∙ ((Q ▷ r) ∙ A)))) =₂
        (((b′ ∙ d) ∙ eH) ∙ ((w ∙ (Q ▷ r)) ∙ A))
      regroup = isoComp-cong (idIso ((b′ ∙ d) ∙ eH))
          ((isoComp-assoc-at w (Q ▷ r) A) ⁻¹) ∙
        ((isoComp-assoc-at (b′ ∙ d) eH (w ∙ ((Q ▷ r) ∙ A))) ⁻¹ ∙
        (isoComp-cong (idIso (b′ ∙ d)) (isoComp-assoc-at eH w ((Q ▷ r) ∙ A)) ∙
          (isoComp-assoc-at b′ d ((eH ∙ w) ∙ ((Q ▷ r) ∙ A))) ⁻¹))

      normalized : (b′ ∙ ((θ ▷ i) ∙ Qr)) =₂
        (u ∙ (((b ∙ evaluate-curry z H) ▷ r) ∙ A))
      normalized = isoComp-cong (idIso u)
          (isoComp-cong ((preWhisker-isoComp-at b (evaluate-curry z H) r) ⁻¹) (idIso A)) ∙
        isoComp-cong (idIso u)
          ((isoComp-assoc-at jβ (evaluate-curry z H ▷ r) A) ⁻¹ ∙
            isoComp-cong (idIso jβ)
              (isoComp-cong ((preWhisker-isoComp-at (β ▷ j) Q r) ⁻¹) (idIso A))) ∙
        isoComp-assoc-at u jβ ((w ∙ (Q ▷ r)) ∙ A) ∙
        isoComp-cong projection (idIso ((w ∙ (Q ▷ r)) ∙ A)) ∙
        regroup ∙
        isoComp-cong (idIso b′)
          (isoComp-cong (idIso d) (isoComp-cong changed-evaluation (idIso ((Q ▷ r) ∙ A)))) ∙
        isoComp-cong (idIso b′) raw-image

      comparison : ((identity-boundary z r ∙ evaluate-curry z K) ∙
          (evaluate z ◁ δ)) =₂
        (u ∙ (((b ∙ evaluate-curry z H) ▷ r) ∙ A))
      comparison = normalized ∙
        (isoComp-cong (idIso b′) Reflected.endpoint ∙
          isoComp-assoc-at b′ (evaluate-curry z K) (evaluate z ◁ δ))

  comparison : ExpressionIso (record
    { arrow = identityArrow ∘ r
    ; source-frame = constant-frame ev₀ identity-source r
    ; target-frame = constant-frame ev₁ identity-target r }) (identity-expression r)
  comparison = record
    { comparison = δ
    ; source-compatible = Endpoint.comparison zero
    ; target-compatible = Endpoint.comparison one }

constant-isomorphism-comparison : {Γ C : CAT} {x y : MAP Γ C}
  (α : x =₁ y) → ExpressionIso (constant-identification α) (isomorphism-expression α)
constant-isomorphism-comparison {x = x} α = record
  { comparison = A.comparison
  ; source-compatible = A.source-compatible
  ; target-compatible = isoComp-cong (idIso α) A.target-compatible ∙
      isoComp-assoc-at α (MorphismExpression.target-frame (identity-expression x))
        (ev₁ ◁ A.comparison) }
  where module A = ExpressionIso (At.comparison x)
```
