# Normalizing the one-sided pullback square

This supporting calculation projects the matching of a directed-pullback
cone onto the retained endpoint. It compares the full pasted square
with the square whose matching is the original endpoint frame.
Both the projection comparisons and the matching compatibility are kept.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section01.EvaluationCalculus.EndpointNormalization
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter04.Section01.EvaluationCalculus.EndpointPullbacks 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M using (productMap-pair)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange 𝒯
  using (changeLeft; changeLeft-pre; changeLeft-iso)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-inverse)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.Comparisons 𝒯
  using (coneIso-compose; coneIso-inverse)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as PU
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pair-pre-cong-triangle₁; pair-pre-cong-triangle₂)
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (project-composite; cancel-right)

module SourceNormalization {A B Γ : CAT} (f : MAP A B)
  (x : MAP Γ A) (y : MAP Γ B)
  (α : MorphismExpression (f ∘ x) (id B ∘ y)) where
  module D = Evaluation.Left f
  module Endpoint = Source f
  module α = MorphismExpression α
  input = D.cone x y α
  normalized = changeLeft (pair-β₁ ev₀ ev₁) (Endpoint.Paste.Paste.flatten input)
  standard : Cone (ev₀ {B}) f Γ
  standard = record { left = α.arrow ; right = x ; match = α.source-frame }

  private
    p = α.arrow
    q = pair x y
    k = pr₁ {B} {B}
    b = pair-β₁ (f ∘ pr₁) (id B ∘ pr₂)
    b′ = (b ⁻¹) ⁻¹
    aAssoc = comp-assoc q pr₁ f
    bAssoc = comp-assoc q (productMap f (id B)) k
    F = f ◁ pair-β₁ x y
    U = (b ▷ q) ∙ bAssoc ⁻¹
    U′ = (b′ ▷ q) ∙ bAssoc ⁻¹
    H = productMap-pair f (id B) x y
    Q = pair-cong α.source-frame α.target-frame ∙ pair-pre ev₀ ev₁ p
    τ = H ⁻¹ ∙ Q
    δ = k ◁ τ
    cAssoc = comp-assoc p endpoints k
    t = pair-β₁ ev₀ ev₁ ▷ p
    s = α.source-frame
    V = t ∙ cAssoc ⁻¹
    bCod = pair-β₁ (f ∘ x) (id B ∘ y)
    Z = (F ∙ aAssoc) ∙ U

    abstract
      hProj : (bCod ∙ (k ◁ H)) =₂ Z
      hProj = pair-pre-cong-triangle₁ (f ∘ pr₁) (id B ∘ pr₂) q
        ((f ◁ pair-β₁ x y) ∙ comp-assoc q pr₁ f)
        (((id B) ◁ pair-β₂ x y) ∙ comp-assoc q pr₂ (id B))

    abstract
      qProj : (bCod ∙ (k ◁ Q)) =₂ (s ∙ V)
      qProj = pair-pre-cong-triangle₁ ev₀ ev₁ p α.source-frame α.target-frame

    abstract
      uproof : U′ =₂ U
      uproof = isoComp-cong (preWhisker q ◁ inverse-inverse b) (idIso (bAssoc ⁻¹))

    abstract
      hcancel : (H ∙ τ) =₂ Q
      hcancel = isoComp-unitˡ-at Q ∙
        (isoComp-cong (isoComp-inverseʳ-at H) (idIso Q) ∙
          (isoComp-assoc-at H (H ⁻¹) Q) ⁻¹)

    abstract
      core : (Z ∙ δ) =₂ (s ∙ V)
      core = qProj ∙
        (isoComp-cong (idIso bCod) (postWhisker k ◁ hcancel) ∙
          ((project-composite k H τ bCod) ⁻¹ ∙ isoComp-cong (hProj ⁻¹) (idIso δ)))

    abstract
      inner : (F ∙ ((aAssoc ∙ U′) ∙ (δ ∙ cAssoc))) =₂ ((Z ∙ δ) ∙ cAssoc)
      inner = (isoComp-assoc-at Z δ cAssoc) ⁻¹ ∙
        (isoComp-cong
          (isoComp-cong (idIso (F ∙ aAssoc)) uproof ∙ (isoComp-assoc-at F aAssoc U′) ⁻¹)
          (idIso (δ ∙ cAssoc)) ∙
          (isoComp-assoc-at F (aAssoc ∙ U′) (δ ∙ cAssoc)) ⁻¹)

    abstract
      reassociate : (F ∙ Cone.match normalized) =₂ (((Z ∙ δ) ∙ cAssoc) ∙ t ⁻¹)
      reassociate = isoComp-cong inner (idIso (t ⁻¹)) ∙
        (isoComp-assoc-at F ((aAssoc ∙ U′) ∙ (δ ∙ cAssoc)) (t ⁻¹)) ⁻¹

    abstract
      dropC : ((s ∙ V) ∙ cAssoc) =₂ (s ∙ t)
      dropC = isoComp-unitʳ-at (s ∙ t) ∙
        (isoComp-cong (idIso (s ∙ t)) (isoComp-inverseˡ-at cAssoc) ∙
          (isoComp-assoc-at (s ∙ t) (cAssoc ⁻¹) cAssoc ∙
            isoComp-cong ((isoComp-assoc-at s t (cAssoc ⁻¹)) ⁻¹) (idIso cAssoc)))

    abstract
      normal : (F ∙ Cone.match normalized) =₂ s
      normal = cancel-right t s ∙
        (isoComp-cong dropC (idIso (t ⁻¹)) ∙
          (isoComp-cong (isoComp-cong core (idIso cAssoc)) (idIso (t ⁻¹)) ∙ reassociate))

  comparison : ConeIso normalized standard
  comparison = record
    { leftIso = idIso p ; rightIso = pair-β₁ x y
    ; compatible = normal ⁻¹ ∙
        (isoComp-unitʳ-at s ∙ isoComp-cong (idIso s) (postWhisker-idIso ev₀ p)) }

module TargetNormalization {A B Γ : CAT} (f : MAP A B)
  (x : MAP Γ B) (y : MAP Γ A)
  (α : MorphismExpression (id B ∘ x) (f ∘ y)) where
  module D = Evaluation.Right f
  module Endpoint = Target f
  module α = MorphismExpression α
  input = D.cone x y α
  normalized = changeLeft (pair-β₂ ev₀ ev₁) (Endpoint.Paste.Paste.flatten input)
  standard : Cone (ev₁ {B}) f Γ
  standard = record { left = α.arrow ; right = y ; match = α.target-frame }

  private
    p = α.arrow
    q = pair x y
    k = pr₂ {B} {B}
    b = pair-β₂ (id B ∘ pr₁) (f ∘ pr₂)
    b′ = (b ⁻¹) ⁻¹
    aAssoc = comp-assoc q pr₂ f
    bAssoc = comp-assoc q (productMap (id B) f) k
    F = f ◁ pair-β₂ x y
    U = (b ▷ q) ∙ bAssoc ⁻¹
    U′ = (b′ ▷ q) ∙ bAssoc ⁻¹
    H = productMap-pair (id B) f x y
    Q = pair-cong α.source-frame α.target-frame ∙ pair-pre ev₀ ev₁ p
    τ = H ⁻¹ ∙ Q
    δ = k ◁ τ
    cAssoc = comp-assoc p endpoints k
    t = pair-β₂ ev₀ ev₁ ▷ p
    s = α.target-frame
    V = t ∙ cAssoc ⁻¹
    bCod = pair-β₂ (id B ∘ x) (f ∘ y)
    Z = (F ∙ aAssoc) ∙ U

    abstract
      hProj : (bCod ∙ (k ◁ H)) =₂ Z
      hProj = pair-pre-cong-triangle₂ (id B ∘ pr₁) (f ∘ pr₂) q
        (((id B) ◁ pair-β₁ x y) ∙ comp-assoc q pr₁ (id B))
        ((f ◁ pair-β₂ x y) ∙ comp-assoc q pr₂ f)

    abstract
      qProj : (bCod ∙ (k ◁ Q)) =₂ (s ∙ V)
      qProj = pair-pre-cong-triangle₂ ev₀ ev₁ p α.source-frame α.target-frame

    abstract
      uproof : U′ =₂ U
      uproof = isoComp-cong (preWhisker q ◁ inverse-inverse b) (idIso (bAssoc ⁻¹))

    abstract
      hcancel : (H ∙ τ) =₂ Q
      hcancel = isoComp-unitˡ-at Q ∙
        (isoComp-cong (isoComp-inverseʳ-at H) (idIso Q) ∙
          (isoComp-assoc-at H (H ⁻¹) Q) ⁻¹)

    abstract
      core : (Z ∙ δ) =₂ (s ∙ V)
      core = qProj ∙
        (isoComp-cong (idIso bCod) (postWhisker k ◁ hcancel) ∙
          ((project-composite k H τ bCod) ⁻¹ ∙ isoComp-cong (hProj ⁻¹) (idIso δ)))

    abstract
      inner : (F ∙ ((aAssoc ∙ U′) ∙ (δ ∙ cAssoc))) =₂ ((Z ∙ δ) ∙ cAssoc)
      inner = (isoComp-assoc-at Z δ cAssoc) ⁻¹ ∙
        (isoComp-cong
          (isoComp-cong (idIso (F ∙ aAssoc)) uproof ∙ (isoComp-assoc-at F aAssoc U′) ⁻¹)
          (idIso (δ ∙ cAssoc)) ∙
          (isoComp-assoc-at F (aAssoc ∙ U′) (δ ∙ cAssoc)) ⁻¹)

    abstract
      reassociate : (F ∙ Cone.match normalized) =₂ (((Z ∙ δ) ∙ cAssoc) ∙ t ⁻¹)
      reassociate = isoComp-cong inner (idIso (t ⁻¹)) ∙
        (isoComp-assoc-at F ((aAssoc ∙ U′) ∙ (δ ∙ cAssoc)) (t ⁻¹)) ⁻¹

    abstract
      dropC : ((s ∙ V) ∙ cAssoc) =₂ (s ∙ t)
      dropC = isoComp-unitʳ-at (s ∙ t) ∙
        (isoComp-cong (idIso (s ∙ t)) (isoComp-inverseˡ-at cAssoc) ∙
          (isoComp-assoc-at (s ∙ t) (cAssoc ⁻¹) cAssoc ∙
            isoComp-cong ((isoComp-assoc-at s t (cAssoc ⁻¹)) ⁻¹) (idIso cAssoc)))

    abstract
      normal : (F ∙ Cone.match normalized) =₂ s
      normal = cancel-right t s ∙
        (isoComp-cong dropC (idIso (t ⁻¹)) ∙
          (isoComp-cong (isoComp-cong core (idIso cAssoc)) (idIso (t ⁻¹)) ∙ reassociate))

  comparison : ConeIso normalized standard
  comparison = record
    { leftIso = idIso p ; rightIso = pair-β₂ x y
    ; compatible = normal ⁻¹ ∙
        (isoComp-unitʳ-at s ∙ isoComp-cong (idIso s) (postWhisker-idIso ev₁ p)) }
```

