# Interval parameters over the base

Product symmetry changes the order of the interval and the domain. Its
restriction to an endpoint agrees with interval insertion as a functor
over the base, including the specified projection comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares as Projections
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter03.RelativeCategories.Families.IntervalParameters
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I
open import SCT.VolumeI.Chapter01.Section04.Points 𝒯 M using (oneProduct-in; oneProduct-retraction)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.NativePointFamilies 𝒯 M ℱ P
  using (point-parameter)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-inverse)
module PS = Projections 𝒯

private
  abstract
    reduced-compose : {X Y C B : CAT} (p : MAP C B) (π : MAP Y C)
      (g : MAP X Y) {q : MAP X C} (bg : (π ∘ g) =₁ q)
      (f : MAP C X) (bf : (q ∘ f) =₁ id C) →
      PS.compose-base (p ∘ π) g (PS.lift-base p π g bg) f
        (comp-unitʳ p ∙ PS.lift-base p q f bf) =₂
      (comp-unitʳ p ∙ PS.lift-base p π (g ∘ f) (PS.compose-base π g bg f bf))
    reduced-compose p π g {q} bg f bf =
      isoComp-cong (idIso (comp-unitʳ p)) (PS.lift-compose p π g f bg bf) ∙
      isoComp-assoc-at (comp-unitʳ p) (PS.lift-base p q f bf)
        ((PS.lift-base p π g bg ▷ f) ∙ (comp-assoc f g (p ∘ π)) ⁻¹)

module At {C B : CAT} (p : MAP C B) where
  symmetry : FunctorOver (p ∘ pr₂ {C = [1]}) (p ∘ pr₁ {C = C} {D = [1]})
  symmetry = record
    { lift = swap
    ; comparison = PS.lift-base p pr₁ swap (pair-β₁ pr₂ pr₁) }

  inverse-symmetry : FunctorOver (p ∘ pr₁ {C = C} {D = [1]}) (p ∘ pr₂ {C = [1]})
  inverse-symmetry = record
    { lift = swap
    ; comparison = PS.lift-base p pr₂ swap (pair-β₂ pr₂ pr₁) }

  insertion : (z : Obj-abs [1]) → FunctorOver p (p ∘ pr₁ {C = C} {D = [1]})
  insertion z = record { lift = insert z ; comparison = identity-boundary z p }

  module Endpoint (z : Obj-abs [1]) where
    t = oneProduct-in C
    r = productMap z (id C)
    h = swap {C = [1]} {D = C}
    j = r ∘ t
    bt = oneProduct-retraction C
    br = comp-unitˡ pr₂ ∙ pair-β₂ (z ∘ pr₁) (id C ∘ pr₂)
    bh : (pr₁ ∘ h) =₁ pr₂
    bh = pair-β₁ pr₂ pr₁
    bj = PS.compose-base pr₂ r br t bt
    b = PS.compose-base pr₁ h bh j bj
    end = pair-β₁ (id C) (z ∘ terminate C)

    second-parameter : (pr₁ ∘ j) =₁ (z ∘ terminate C)
    second-parameter = (z ◁ terminal-iso (pr₁ ∘ t) (terminate C)) ∙
      (comp-assoc t pr₁ z ∙
        ((pair-β₁ (z ∘ pr₁) (id C ∘ pr₂) ▷ t) ∙ (comp-assoc t r pr₁) ⁻¹))

    second : (pr₂ ∘ (h ∘ j)) =₁ (z ∘ terminate C)
    second = second-parameter ∙
      ((pair-β₂ pr₂ pr₁ ▷ j) ∙ (comp-assoc j h pr₂) ⁻¹)

    first-comparison = end ⁻¹ ∙ b
    second-comparison = (pair-β₂ (id C) (z ∘ terminate C)) ⁻¹ ∙ second
    underlying : (h ∘ j) =₁ insert z
    underlying = pair-iso first-comparison second-comparison

    abstract
      projection : (end ∙ (pr₁ ◁ underlying)) =₂ b
      projection = cancel-inverse end b ∙
        isoComp-cong (idIso end) (pair-iso-β₁ first-comparison second-comparison)

      parameter-frame : FunctorLift.comparison (point-parameter p z) =₂
        (comp-unitʳ p ∙ PS.lift-base p pr₂ j bj)
      parameter-frame = reduced-compose p pr₂ r br t bt

      symmetry-frame : FunctorLift.comparison (compose-over symmetry (point-parameter p z)) =₂
        (comp-unitʳ p ∙ PS.lift-base p pr₁ (h ∘ j) b)
      symmetry-frame = reduced-compose p pr₁ h bh j bj ∙
        isoComp-cong parameter-frame
          (idIso ((FunctorLift.comparison symmetry ▷ j) ∙ (comp-assoc j h (p ∘ pr₁)) ⁻¹))

      comparison : FunctorOverIso (compose-over symmetry (point-parameter p z)) (insertion z)
      comparison = record
        { underlying = underlying
        ; compatible = symmetry-frame ⁻¹ ∙
            isoComp-cong (idIso (comp-unitʳ p)) (PS.lift-square p pr₁ b end underlying projection) ∙
            isoComp-assoc-at (comp-unitʳ p) (PS.lift-base p pr₁ (insert z) end)
              ((p ∘ pr₁) ◁ underlying) }

    h′ = swap {C = C} {D = [1]}
    bh′ : (pr₂ ∘ h′) =₁ pr₁
    bh′ = pair-β₂ pr₂ pr₁
    back = PS.compose-base pr₂ h′ bh′ (insert z) end
    back-parameter : (pr₁ ∘ (h′ ∘ insert z)) =₁ (z ∘ terminate C)
    back-parameter = pair-β₂ (id C) (z ∘ terminate C) ∙
      ((pair-β₁ pr₂ pr₁ ▷ insert z) ∙ (comp-assoc (insert z) h′ pr₁) ⁻¹)
    reverse-first = second-parameter ⁻¹ ∙ back-parameter
    reverse-second = bj ⁻¹ ∙ back
    reverse-underlying : (h′ ∘ insert z) =₁ j
    reverse-underlying = pair-iso reverse-first reverse-second

    abstract
      reverse-projection : (bj ∙ (pr₂ ◁ reverse-underlying)) =₂ back
      reverse-projection = cancel-inverse bj back ∙
        isoComp-cong (idIso bj) (pair-iso-β₂ reverse-first reverse-second)

      reverse-frame : FunctorLift.comparison (compose-over inverse-symmetry (insertion z)) =₂
        (comp-unitʳ p ∙ PS.lift-base p pr₂ (h′ ∘ insert z) back)
      reverse-frame = reduced-compose p pr₂ h′ bh′ (insert z) end

      reverse-comparison : FunctorOverIso (compose-over inverse-symmetry (insertion z)) (point-parameter p z)
      reverse-comparison = record
        { underlying = reverse-underlying
        ; compatible = reverse-frame ⁻¹ ∙
            isoComp-cong (idIso (comp-unitʳ p))
              (PS.lift-square p pr₂ back bj reverse-underlying reverse-projection) ∙
            isoComp-assoc-at (comp-unitʳ p) (PS.lift-base p pr₂ j bj)
              ((p ∘ pr₂) ◁ reverse-underlying) ∙
            isoComp-cong parameter-frame (idIso ((p ∘ pr₂) ◁ reverse-underlying)) }
```
