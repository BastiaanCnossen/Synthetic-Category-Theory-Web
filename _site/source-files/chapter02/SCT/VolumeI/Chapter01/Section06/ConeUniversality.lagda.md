# Comparing universal cones

A complete identification of cones identifies their actual chosen pullback
comparisons. Equivalence of that comparison therefore transports along the
identification, retaining the supplied matching boundary.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.ConeUniversality where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (comp₌-inverseʳ-One; comp₌-unitˡ-One; preWhisker-inverse)
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
open import SCT.VolumeI.Chapter01.Section06.ConeTransport
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (equiv-transport)
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares

module _ {Γ : Context} where
  isPullback-cone-identification : {C D E S : CAT Γ} {f : MAP C E} {g : MAP D E}
    {s t : Cone f g S} → ConeIdentification₁ s t → IsPullback s → IsPullback t
  isPullback-cone-identification Φ e = equiv-transport (pullback-factor-cong Φ) e
```


## Universality under right-arrow change

The source universal cone factors the inverse-changed target cone. Changing
its complete beta back supplies the target factor. Reflection reverses the
same change using its complete inverse and restriction comparisons.

```agda
  module RightArrowChange {C D E S : CAT Γ} {f : MAP C E} {g g′ : MAP D E}
    (δ : g =₁ g′) (s : Cone f g S) (e : IsPullback s) where
    private
      module Source = UniversalCone s e

      roundtrip : {T : CAT Γ} (t : Cone f g′ T)
        → ConeIdentification₁ (cone-change-right δ (cone-change-right (δ ⁻¹) t)) t
      roundtrip t = cone-retarget-match-identification _ (Cone.match t)
        (comp₌-unitˡ-One (Cone.match t) ∙
          (comp₌-cong (comp₌-inverseʳ-One (δ ▷ Cone.right t)) (id₌ (Cone.match t)) ∙
            ((comp₌-assoc (δ ▷ Cone.right t) ((δ ▷ Cone.right t) ⁻¹) (Cone.match t)) ⁻¹ ∙
              comp₌-cong (id₌ (δ ▷ Cone.right t))
                (comp₌-cong (preWhisker-inverse δ (Cone.right t)) (id₌ (Cone.match t))))))

    factor : {T : CAT Γ} → Cone f g′ T → MAP T S
    factor t = Source.factor (cone-change-right (δ ⁻¹) t)

    β : {T : CAT Γ} (t : Cone f g′ T)
      → ConeIdentification₁ (cone-restrict (factor t) (cone-change-right δ s)) t
    β t = cone-compose (roundtrip t)
      (cone-compose (cone-change-right-identification δ (Source.β (cone-change-right (δ ⁻¹) t)))
        (cone-change-right-restrict δ (factor t) s))

    reflect : {T : CAT Γ} (h k : MAP T S)
      → ConeIdentification₁ (cone-restrict h (cone-change-right δ s))
          (cone-restrict k (cone-change-right δ s)) → h =₁ k
    reflect h k Φ = Source.reflect h k
      (cone-compose (cone-change-right-inverse δ (cone-restrict k s))
        (cone-compose (cone-change-right-identification (δ ⁻¹) (cone-change-right-restrict δ k s))
          (cone-compose (cone-change-right-identification (δ ⁻¹) Φ)
            (cone-compose (cone-change-right-identification (δ ⁻¹)
                (cone-inverse (cone-change-right-restrict δ h s)))
              (cone-inverse (cone-change-right-inverse δ (cone-restrict h s)))))))

    isPullback : IsPullback (cone-change-right δ s)
    isPullback = pullback-recognize (cone-change-right δ s) factor β reflect
```

## Universality under symmetry

The original universal cone factors the swapped target cone. Swapping its
complete beta back and cancelling double symmetry gives the new beta.
Reflection uses the same full comparisons in the opposite direction.

```agda
  module SwappedCone {C D E S : CAT Γ} {f : MAP C E} {g : MAP D E}
    (s : Cone f g S) (e : IsPullback s) where
    private
      module Original = UniversalCone s e

    factor : {T : CAT Γ} → Cone g f T → MAP T S
    factor t = Original.factor (cone-swap t)

    β : {T : CAT Γ} (t : Cone g f T)
      → ConeIdentification₁ (cone-restrict (factor t) (cone-swap s)) t
    β t = cone-compose (cone-swap-twice t)
      (cone-compose (cone-swap-identification (Original.β (cone-swap t)))
        (cone-swap-restrict (factor t) s))

    reflect : {T : CAT Γ} (h k : MAP T S)
      → ConeIdentification₁ (cone-restrict h (cone-swap s))
          (cone-restrict k (cone-swap s)) → h =₁ k
    reflect h k Φ = Original.reflect h k
      (cone-compose (cone-swap-twice (cone-restrict k s))
        (cone-compose (cone-swap-identification (cone-swap-restrict k s))
          (cone-compose (cone-swap-identification Φ)
            (cone-compose (cone-swap-identification (cone-inverse (cone-swap-restrict h s)))
              (cone-inverse (cone-swap-twice (cone-restrict h s)))))))

    isPullback : IsPullback (cone-swap s)
    isPullback = pullback-recognize (cone-swap s) factor β reflect

  isPullback-change-left : {C D E S : CAT Γ} {f f′ : MAP C E} {g : MAP D E}
    (δ : f =₁ f′) (s : Cone f g S) → IsPullback s → IsPullback (cone-change-left δ s)
  isPullback-change-left δ s e = SwappedCone.isPullback _
    (RightArrowChange.isPullback δ (cone-swap s) (SwappedCone.isPullback s e))
```
