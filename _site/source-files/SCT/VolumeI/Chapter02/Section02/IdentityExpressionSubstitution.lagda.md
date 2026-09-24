# Identity expressions under substitution

Identity diagrams restrict to identity diagrams. Both endpoint equations
below use the specified insertion square and its first projection witness.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.IdentityExpressionSubstitution
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section02.DirectUnitTriangles 𝒯 M ℱ P I E
  using (module ReflectedEndpoint)
open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter01.Section07.IsomorphismLifting 𝒯 M ℱ
  using (funIsoReflect; funIsoReflect-β)
open import SCT.VolumeI.Chapter02.Section02.InsertionEvaluation 𝒯 M ℱ
  using (evaluate-insertion; evaluate-uncurry-compose)
open import SCT.VolumeI.Chapter01.Section04.SquareEvaluation 𝒯 M using (change-evaluation)
import SCT.VolumeI.Chapter01.Section04.SplitProjectionNaturality as Split
import SCT.VolumeI.Chapter02.Section02.InsertionProjectionWitnesses as Insertion

module Restrict {Γ Δ C : CAT} (x : MAP Γ C) (r : MAP Δ Γ) where
  H = x ∘ pr₁ {C = Γ} {D = [1]}
  K = (x ∘ r) ∘ pr₁ {C = Δ} {D = [1]}
  F = funCurry H
  G = funCurry K
  R = productMap r (id [1])
  bR = pair-β₁ (r ∘ pr₁) (id [1] ∘ pr₂)
  D = (comp-assoc pr₁ r x) ⁻¹ ∙ ((x ◁ bR) ∙ comp-assoc R pr₁ x)
  β = funCurry-β H
  U = funUncurry-restrict F r
  θ = D ∙ ((β ▷ R) ∙ U)
  raw = (funCurry-β K) ⁻¹ ∙ θ
  δ = funIsoReflect (F ∘ r) G raw

  module Endpoint (z : Obj-abs [1]) where
    i = insert {X = Δ} z
    j = insert {X = Γ} z
    module Projection = Insertion.Parameter 𝒯 M ℱ r z
    module Boundary = Split.Along 𝒯 M pr₁ pr₁ i j (pair-β₁ _ _) (pair-β₁ _ _)
      r R bR (insert-natural r z) Projection.projection₁ x
    module Reflected = ReflectedEndpoint z (F ∘ r) G (funCurry-β K) θ δ
      (funIsoReflect-β (F ∘ r) G raw)
    Q = evaluate-uncurry z F
    Qr = evaluate-uncurry z (F ∘ r)
    A = (comp-assoc r F (evaluate z)) ⁻¹
    e = evaluate-insertion (funUncurry F) r z
    eH = evaluate-insertion H r z
    b = identity-boundary z x
    b′ = identity-boundary z (x ∘ r)
    d = D ▷ i
    v = (β ▷ R) ▷ i
    w = (β ▷ j) ▷ r

    abstract
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
        (((b ∙ evaluate-curry z H) ▷ r) ∙ A)
      normalized =
        isoComp-cong ((preWhisker-isoComp-at b (evaluate-curry z H) r) ⁻¹) (idIso A) ∙
        (isoComp-assoc-at (b ▷ r) (evaluate-curry z H ▷ r) A) ⁻¹ ∙
        isoComp-cong (idIso (b ▷ r))
          (isoComp-cong ((preWhisker-isoComp-at (β ▷ j) Q r) ⁻¹) (idIso A)) ∙
        isoComp-cong Boundary.comparison (idIso ((w ∙ (Q ▷ r)) ∙ A)) ∙
        regroup ∙
        isoComp-cong (idIso b′)
          (isoComp-cong (idIso d) (isoComp-cong changed-evaluation (idIso ((Q ▷ r) ∙ A)))) ∙
        isoComp-cong (idIso b′) raw-image

      comparison : ((identity-boundary z (x ∘ r) ∙ evaluate-curry z K) ∙
          (evaluate z ◁ δ)) =₂
        (((identity-boundary z x ∙ evaluate-curry z H) ▷ r) ∙ A)
      comparison = normalized ∙
        (isoComp-cong (idIso b′) Reflected.endpoint ∙
          isoComp-assoc-at b′ (evaluate-curry z K) (evaluate z ◁ δ))

  comparison : ExpressionIso (restrict-expression (identity-expression x) r) (identity-expression (x ∘ r))
  comparison = record
    { comparison = δ
    ; source-compatible = Endpoint.comparison zero
    ; target-compatible = Endpoint.comparison one }
```
