# The comparison with a nested pullback

These are the two functors in part (1) of `lem:Pasting_Lemma_Pullbacks`.
Their cone comparisons retain the three chosen matching isomorphisms.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section05.NestedPullbacks
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section05.ConePasting 𝒯
open import SCT.VolumeI.Chapter01.Section05.PullbackLifting 𝒯 P
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left; cancel-right)

module Nested {A B X Z : CAT} (f : MAP A B) (g : MAP B Z) (h : MAP X Z) where

  Q = Pullback g h
  Outer = Pullback (g ∘ f) h
  u : MAP Q B
  u = pb₁
  v : MAP Q X
  v = pb₂
  N = Pullback f u
  outerCone = pbCone (g ∘ f) h
  nestedCone = pbCone f u
  outerLeft = Cone.left outerCone
  b = Cone.right outerCone
  ℓ = Cone.left nestedCone
  r = Cone.right nestedCone
  ρ = Cone.match nestedCone
  module Paste = PasteCones f g (pbCone g h)

  flatCone = Paste.flatten nestedCone
  flatten : MAP N Outer
  flatten = pbLift flatCone
  α = pbLift-β₁ flatCone
  β = pbLift-β₂ flatCone

  innerCone = compositeCone f g outerCone
  inner : MAP Outer Q
  inner = pbLift innerCone
  δ = pbLift-β₁ innerCone
  ε = pbLift-β₂ innerCone

  insertionCone : Cone f u Outer
  insertionCone = record { left = outerLeft ; right = inner ; match = invIso δ }
  insert : MAP Outer N
  insert = pbLift insertionCone

  δF = (δ ▷ flatten) ∙ invIso (comp-assoc flatten inner u)
  εF = (ε ▷ flatten) ∙ invIso (comp-assoc flatten inner v)
  κ = ρ ∙ ((f ◁ α) ∙ comp-assoc flatten outerLeft f)

  inner-comparison-raw : ConeIso (conePre (inner ∘ flatten) (pbCone g h)) (conePre r (pbCone g h))
  inner-comparison-raw = coneIso-compose (Paste.flatten-composite nestedCone)
    (coneIso-compose (compositeConeIso f g (pbLift-β flatCone))
    (coneIso-compose (compositeCone-pre f g flatten outerCone)
    (coneIso-compose (coneIso-pre flatten (pbLift-β innerCone))
      (coneIso-inverse (conePre-assoc flatten inner (pbCone g h))))))

  inner-comparison : ConeIso (conePre (inner ∘ flatten) (pbCone g h)) (conePre r (pbCone g h))
  inner-comparison = coneIso-adjust inner-comparison-raw (κ ∙ δF) (β ∙ εF)
    (invIso (isoComp-assoc-at ρ ((f ◁ α) ∙ comp-assoc flatten outerLeft f) δF) ∙
      isoComp-cong (idIso ρ) (invIso (isoComp-assoc-at (f ◁ α) (comp-assoc flatten outerLeft f) δF)))
    (isoComp-cong (idIso β) (isoComp-unitˡ-at εF) ∙ isoComp-unitˡ-at (β ∙ (idIso _ ∙ εF)))

  module InnerLift = Lift (inner ∘ flatten) r inner-comparison
  χ = InnerLift.lift

  insertion-comparison : ConeIso (conePre flatten insertionCone) nestedCone
  insertion-comparison = record
    { leftIso = α ; rightIso = χ
    ; compatible = isoComp-cong (invIso InnerLift.left-image) (idIso ω) ∙ invIso cancel }
    where
    assocLeft = comp-assoc flatten outerLeft f
    assocRight = comp-assoc flatten inner u
    d = δ ▷ flatten
    d′ = invIso δ ▷ flatten
    ω = Cone.match (conePre flatten insertionCone)
    imageInverse = preWhisker-idIso (f ∘ outerLeft) flatten ∙
      ((preWhisker flatten ◁ isoComp-inverseʳ-at δ) ∙
        invIso (preWhisker-isoComp-at δ (invIso δ) flatten))
    cancelTransport : Iso₂ (δF ∙ ω) (invIso assocLeft)
    cancelTransport = isoComp-unitˡ-at (invIso assocLeft) ∙
      (isoComp-cong imageInverse (idIso (invIso assocLeft)) ∙
      (invIso (isoComp-assoc-at d d′ (invIso assocLeft)) ∙
      (isoComp-cong (idIso d) (cancel-left assocRight (d′ ∙ invIso assocLeft)) ∙
        isoComp-assoc-at d (invIso assocRight) ω)))
    cancel : Iso₂ ((κ ∙ δF) ∙ ω) (ρ ∙ (f ◁ α))
    cancel = cancel-right assocLeft (ρ ∙ (f ◁ α)) ∙
      (isoComp-cong (invIso (isoComp-assoc-at ρ (f ◁ α) assocLeft)) (idIso (invIso assocLeft)) ∙
      (isoComp-cong (idIso κ) cancelTransport ∙ isoComp-assoc-at κ δF ω))

  insert-flatten : NatIso (insert ∘ flatten) (id N)
  insert-flatten = pullback-reflect _ _
    (coneIso-compose (coneIso-inverse (conePre-id nestedCone))
    (coneIso-compose insertion-comparison
    (coneIso-compose (coneIso-pre flatten (pbLift-β insertionCone))
      (coneIso-inverse (conePre-assoc flatten insert nestedCone)))))

  flatten-insertion : ConeIso (Paste.flatten insertionCone) outerCone
  flatten-insertion = compositeCone-compatible f g _ _ (idIso outerLeft) ε
    (isoComp-cong (idIso (h ◁ ε)) (invIso (Paste.flatten-match insertionCone)) ∙
      (isoComp-assoc-at (h ◁ ε) ν (g ◁ invIso δ) ∙
      (invIso cancel ∙
      (isoComp-unitʳ-at σ ∙ isoComp-cong (idIso σ)
        (postWhisker-idIso g (f ∘ outerLeft) ∙ (postWhisker g ◁ postWhisker-idIso f outerLeft))))))
    where
    ν = Cone.match (conePre inner (pbCone g h))
    σ = Cone.match innerCone
    inverseImage = postWhisker-idIso g (f ∘ outerLeft) ∙
      ((postWhisker g ◁ isoComp-inverseʳ-at δ) ∙ invIso (postWhisker-isoComp-at g δ (invIso δ)))
    cancel : Iso₂ (((h ◁ ε) ∙ ν) ∙ (g ◁ invIso δ)) σ
    cancel = isoComp-unitʳ-at σ ∙
      (isoComp-cong (idIso σ) inverseImage ∙
      (isoComp-assoc-at σ (g ◁ δ) (g ◁ invIso δ) ∙
        isoComp-cong (invIso (ConeIso.compatible (pbLift-β innerCone))) (idIso (g ◁ invIso δ))))

  flatten-insert : NatIso (flatten ∘ insert) (id Outer)
  flatten-insert = pullback-reflect _ _
    (coneIso-compose (coneIso-inverse (conePre-id outerCone))
    (coneIso-compose flatten-insertion
    (coneIso-compose (Paste.flatten-iso (pbLift-β insertionCone))
    (coneIso-compose (Paste.flatten-pre insert nestedCone)
    (coneIso-compose (coneIso-pre insert (pbLift-β flatCone))
      (coneIso-inverse (conePre-assoc insert flatten outerCone)))))))

  flatten-isEquiv : IsEquiv flatten
  flatten-isEquiv = record
    { inverse = insert ; sectionIso = invIso insert-flatten ; retractionIso = invIso flatten-insert }

  insert-isEquiv : IsEquiv insert
  insert-isEquiv = record
    { inverse = flatten ; sectionIso = invIso flatten-insert ; retractionIso = invIso insert-flatten }
```
