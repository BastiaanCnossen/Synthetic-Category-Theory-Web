# The comparison with a nested pullback

These are the two functors in part (1) of `lem:Pasting_Lemma_Pullbacks`.
Their cone comparisons retain the three chosen matching isomorphisms.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section06.NestedPullbacks
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.ConePasting 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackLifting 𝒯 P
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left; cancel-right)

module Nested {A B X Z : CAT} (f : MAP A B) (g : MAP B Z) (h : MAP X Z) where

  Q = Pullback g h
  Outer = Pullback (g ∘ f) h
  u : MAP Q B
  u = pullback₁
  v : MAP Q X
  v = pullback₂
  N = Pullback f u
  outerCone = pullbackCone (g ∘ f) h
  nestedCone = pullbackCone f u
  outerLeft = Cone.left outerCone
  b = Cone.right outerCone
  ℓ = Cone.left nestedCone
  r = Cone.right nestedCone
  ρ = Cone.match nestedCone
  module Paste = PasteCones f g (pullbackCone g h)

  flatCone = Paste.flatten nestedCone
  flatten : MAP N Outer
  flatten = pullbackLift flatCone
  α = pullbackLift-β₁ flatCone
  β = pullbackLift-β₂ flatCone

  innerCone = compositeCone f g outerCone
  inner : MAP Outer Q
  inner = pullbackLift innerCone
  δ = pullbackLift-β₁ innerCone
  ε = pullbackLift-β₂ innerCone

  insertionCone : Cone f u Outer
  insertionCone = record { left = outerLeft ; right = inner ; match = δ ⁻¹ }
  insert : MAP Outer N
  insert = pullbackLift insertionCone

  δF = (δ ▷ flatten) ∙ (comp-assoc flatten inner u) ⁻¹
  εF = (ε ▷ flatten) ∙ (comp-assoc flatten inner v) ⁻¹
  κ = ρ ∙ ((f ◁ α) ∙ comp-assoc flatten outerLeft f)

  inner-comparison-raw : ConeIso (conePre (inner ∘ flatten) (pullbackCone g h)) (conePre r (pullbackCone g h))
  inner-comparison-raw = coneIso-compose (Paste.flatten-composite nestedCone)
    (coneIso-compose (compositeConeIso f g (pullbackLift-β flatCone))
    (coneIso-compose (compositeCone-pre f g flatten outerCone)
    (coneIso-compose (coneIso-pre flatten (pullbackLift-β innerCone))
      (coneIso-inverse (conePre-assoc flatten inner (pullbackCone g h))))))

  inner-comparison : ConeIso (conePre (inner ∘ flatten) (pullbackCone g h)) (conePre r (pullbackCone g h))
  inner-comparison = coneIso-adjust inner-comparison-raw (κ ∙ δF) (β ∙ εF)
    ((isoComp-assoc-at ρ ((f ◁ α) ∙ comp-assoc flatten outerLeft f) δF) ⁻¹ ∙
      isoComp-cong (idIso ρ) ((isoComp-assoc-at (f ◁ α) (comp-assoc flatten outerLeft f) δF) ⁻¹))
    (isoComp-cong (idIso β) (isoComp-unitˡ-at εF) ∙ isoComp-unitˡ-at (β ∙ (idIso _ ∙ εF)))

  module InnerLift = Lift (inner ∘ flatten) r inner-comparison
  χ = InnerLift.lift

  insertion-comparison : ConeIso (conePre flatten insertionCone) nestedCone
  insertion-comparison = record
    { leftIso = α ; rightIso = χ
    ; compatible = isoComp-cong (InnerLift.left-image ⁻¹) (idIso ω) ∙ cancel ⁻¹ }
    where
    assocLeft = comp-assoc flatten outerLeft f
    assocRight = comp-assoc flatten inner u
    d = δ ▷ flatten
    d′ = δ ⁻¹ ▷ flatten
    ω = Cone.match (conePre flatten insertionCone)
    imageInverse = preWhisker-idIso (f ∘ outerLeft) flatten ∙
      ((preWhisker flatten ◁ isoComp-inverseʳ-at δ) ∙
        (preWhisker-isoComp-at δ (δ ⁻¹) flatten) ⁻¹)
    cancelTransport : (δF ∙ ω) =₂ (assocLeft ⁻¹)
    cancelTransport = isoComp-unitˡ-at (assocLeft ⁻¹) ∙
      (isoComp-cong imageInverse (idIso (assocLeft ⁻¹)) ∙
      ((isoComp-assoc-at d d′ (assocLeft ⁻¹)) ⁻¹ ∙
      (isoComp-cong (idIso d) (cancel-left assocRight (d′ ∙ assocLeft ⁻¹)) ∙
        isoComp-assoc-at d (assocRight ⁻¹) ω)))
    cancel : ((κ ∙ δF) ∙ ω) =₂ (ρ ∙ (f ◁ α))
    cancel = cancel-right assocLeft (ρ ∙ (f ◁ α)) ∙
      (isoComp-cong ((isoComp-assoc-at ρ (f ◁ α) assocLeft) ⁻¹) (idIso (assocLeft ⁻¹)) ∙
      (isoComp-cong (idIso κ) cancelTransport ∙ isoComp-assoc-at κ δF ω))

  insert-flatten : (insert ∘ flatten) =₁ (id N)
  insert-flatten = pullback-reflect _ _
    (coneIso-compose (coneIso-inverse (conePre-id nestedCone))
    (coneIso-compose insertion-comparison
    (coneIso-compose (coneIso-pre flatten (pullbackLift-β insertionCone))
      (coneIso-inverse (conePre-assoc flatten insert nestedCone)))))

  flatten-insertion : ConeIso (Paste.flatten insertionCone) outerCone
  flatten-insertion = compositeCone-compatible f g _ _ (idIso outerLeft) ε
    (isoComp-cong (idIso (h ◁ ε)) ((Paste.flatten-match insertionCone) ⁻¹) ∙
      (isoComp-assoc-at (h ◁ ε) ν (g ◁ δ ⁻¹) ∙
      (cancel ⁻¹ ∙
      (isoComp-unitʳ-at σ ∙ isoComp-cong (idIso σ)
        (postWhisker-idIso g (f ∘ outerLeft) ∙ (postWhisker g ◁ postWhisker-idIso f outerLeft))))))
    where
    ν = Cone.match (conePre inner (pullbackCone g h))
    σ = Cone.match innerCone
    inverseImage = postWhisker-idIso g (f ∘ outerLeft) ∙
      ((postWhisker g ◁ isoComp-inverseʳ-at δ) ∙ (postWhisker-isoComp-at g δ (δ ⁻¹)) ⁻¹)
    cancel : (((h ◁ ε) ∙ ν) ∙ (g ◁ δ ⁻¹)) =₂ σ
    cancel = isoComp-unitʳ-at σ ∙
      (isoComp-cong (idIso σ) inverseImage ∙
      (isoComp-assoc-at σ (g ◁ δ) (g ◁ δ ⁻¹) ∙
        isoComp-cong ((ConeIso.compatible (pullbackLift-β innerCone)) ⁻¹) (idIso (g ◁ δ ⁻¹))))

  flatten-insert : (flatten ∘ insert) =₁ (id Outer)
  flatten-insert = pullback-reflect _ _
    (coneIso-compose (coneIso-inverse (conePre-id outerCone))
    (coneIso-compose flatten-insertion
    (coneIso-compose (Paste.flatten-iso (pullbackLift-β insertionCone))
    (coneIso-compose (Paste.flatten-pre insert nestedCone)
    (coneIso-compose (coneIso-pre insert (pullbackLift-β flatCone))
      (coneIso-inverse (conePre-assoc insert flatten outerCone)))))))

  flatten-isEquiv : IsEquiv flatten
  flatten-isEquiv = record
    { inverse = insert ; sectionIso = insert-flatten ⁻¹ ; retractionIso = flatten-insert ⁻¹ }

  insert-isEquiv : IsEquiv insert
  insert-isEquiv = record
    { inverse = flatten ; sectionIso = flatten-insert ⁻¹ ; retractionIso = insert-flatten ⁻¹ }
```
