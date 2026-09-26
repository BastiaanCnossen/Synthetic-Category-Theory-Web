# The two components of the join boundary

The zero and one sections form a coproduct decomposition of
`Γ × ∂[1]`. In these coordinates the join boundary has fibers `C` and
`D`, with their original structure functors to `Γ`. The pullback squares
below include their transported commutativity identifications.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Interval

module SCT.VolumeI.Chapter03.Section06.BoundaryCalculus.JoinBoundaryCoordinates
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (B : Coproducts.CoproductStructure 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (U : Universality.CoproductUniversality 𝒯 M B P)
  (I : Interval.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Coproducts.CoproductStructure B
open Pullbacks.PullbackStructure P
open Universality 𝒯 M B P
open CoproductUniversality U
open import SCT.VolumeI.Chapter01.Section05.CoproductCalculus 𝒯 M B
open import SCT.VolumeI.Chapter01.Section06.Distributivity 𝒯 M B P U using (module Distributivity)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback; pullback-cone-invariant)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.Comparisons 𝒯 using (coneRetarget; coneRetarget-β)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P using (degenerate-pullback)
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanPullbacks as Mapped
open import SCT.VolumeI.Chapter03.Section06.PushoutCalculus.JoinSpan 𝒯 M B P U I using (∂[1])
open import SCT.VolumeI.Chapter03.Section06.BoundaryCalculus.JoinBoundary 𝒯 M B P U I using (module Boundary)

module Cover (Γ : CAT) where
  section : MAP One ∂[1] → MAP Γ (Γ × ∂[1])
  section i = pair (id Γ) (const i)
  zero = section in₁
  one = section in₂
  equivalence : MAP (Γ ⊔ Γ) (Γ × ∂[1])
  equivalence = copair zero one
  j : MAP Γ (Γ × One)
  j = pair (id Γ) (terminate Γ)
  module D = Distributivity Γ One One using (distribute; distribute-isEquiv)
  abstract
    component : (i : MAP One ∂[1]) → (productMap (id Γ) i ∘ j) =₁ section i
    component i = pair-cong
      (comp-unitˡ (id Γ) ∙ ((id Γ ◁ pair-β₁ (id Γ) (terminate Γ)) ∙ comp-assoc j pr₁ (id Γ)))
      ((i ◁ pair-β₂ (id Γ) (terminate Γ)) ∙ comp-assoc j pr₂ i) ∙
      pair-pre (id Γ ∘ pr₁) (i ∘ pr₂) j
    comparison : (D.distribute ∘ coproductMap j j) =₁ equivalence
    comparison = copair-cong
      (component in₁ ∙ copair-pre₁ (productMap (id Γ) in₁) (productMap (id Γ) in₂) j)
      (component in₂ ∙ copair-pre₂ (productMap (id Γ) in₁) (productMap (id Γ) in₂) j) ∙
      copair-post (in₁ ∘ j) (in₂ ∘ j) D.distribute
    isEquiv : IsEquiv equivalence
    isEquiv = equiv-transport comparison
      (equiv-compose (coproductMap j j) D.distribute
        (coproductMap-isEquiv j j (equiv-inverse (product-unitʳ-isEquiv Γ))
          (equiv-inverse (product-unitʳ-isEquiv Γ))) D.distribute-isEquiv)
    section-composite : {A : CAT} (p : MAP A Γ) (i : MAP One ∂[1]) →
      (section i ∘ p) =₁ pair p (const i)
    section-composite p i = pair-cong (comp-unitˡ p) (const-pre i p) ∙ pair-pre (id Γ) (const i) p

module Fibers {C D Γ : CAT} (p : MAP C Γ) (q : MAP D Γ) where
  module Covered = Cover Γ using (zero; one; equivalence; isEquiv; section-composite)
  module Original = Boundary p q using (projection)
  projection = Original.projection
  abstract
    projection-comparison : (Covered.equivalence ∘ coproductMap p q) =₁ projection
    projection-comparison = copair-cong
      (Covered.section-composite p in₁ ∙ copair-pre₁ Covered.zero Covered.one p)
      (Covered.section-composite q in₂ ∙ copair-pre₂ Covered.zero Covered.one q) ∙
      copair-post (in₁ ∘ p) (in₂ ∘ q) Covered.equivalence

  module Component {A : CAT} (i : MAP A (Γ ⊔ Γ)) (j : MAP A (Γ × ∂[1]))
    (β : (Covered.equivalence ∘ i) =₁ j)
    {V : CAT} (s : Cone (coproductMap p q) i V) (es : IsPullback s) where
    cospan : CospanMap (coproductMap p q) i projection j
    cospan = record { left = id (C ⊔ D) ; right = id A ; base = Covered.equivalence
      ; leftSquare = projection-comparison ⁻¹ ∙ comp-unitʳ projection
      ; rightSquare = β ⁻¹ ∙ comp-unitʳ j }
    mapped = CospanMap.mapCone cospan s
    module Universal = Mapped.Mapped 𝒯 P cospan
      (degenerate-pullback Covered.isEquiv (Mapped.rightSquareOf 𝒯 P cospan) (id-isEquiv A))
      s es using (isPullback)
    square : Cone projection j V
    square = coneRetarget mapped (Cone.left s) (Cone.right s)
      (comp-unitˡ (Cone.left s)) (comp-unitˡ (Cone.right s))
    abstract
      isPullback : IsPullback square
      isPullback = pullback-cone-invariant
        (coneRetarget-β mapped (Cone.left s) (Cone.right s)
          (comp-unitˡ (Cone.left s)) (comp-unitˡ (Cone.right s)))
        (Universal.isPullback (id-isEquiv (C ⊔ D)))
  module First = Component in₁ Covered.zero (copair-β₁ Covered.zero Covered.one)
    (coneSwap (coproductSquare₁ p q)) (pullback-swap (coproductSquare₁ p q) (inclusion₁-isPullback p q))
    using (square; isPullback)
  module Second = Component in₂ Covered.one (copair-β₂ Covered.zero Covered.one)
    (coneSwap (coproductSquare₂ p q)) (pullback-swap (coproductSquare₂ p q) (inclusion₂-isPullback p q))
    using (square; isPullback)
```
