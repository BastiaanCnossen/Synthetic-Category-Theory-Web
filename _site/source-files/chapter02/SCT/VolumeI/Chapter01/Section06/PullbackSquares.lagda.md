# Universal cone recovery

The sixth pullback field recovers a family of vertex identifications from
its complete cone identification. Factoring the encoded family through the
actual identification restriction retains a specified triangle. The two
pullback betas and restriction associativity then recover the supplied cone,
including its matching square.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.PullbackSquares where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (comp-unitˡ; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
import SCT.VolumeI.Chapter01.Section03.Factorizations as Fact
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (equiv-reflect)

module _ {Γ : Context} where
  module PullbackRecovery {C D E T X : CAT Γ} {f : MAP C E} {g : MAP D E}
    (h k : MAP T (Pullback f g))
    (Φ : ConeIdentification X
      (cone-restrict h (pullback-cone f g))
      (cone-restrict k (pullback-cone f g))) where
    open Terms.Equalities X using (_＝_)
    module J = PullbackIdentifications h k

    encoded-cone : Cone J.Boundary.left-map J.Boundary.right-map X
    encoded-cone = J.Boundary.encode Φ

    encoded : MAP X J.Target
    encoded = pullback-factor encoded-cone

    chosen : Fact.Factorization J.restriction encoded
    chosen = Fact.factor-through-equiv (pullback-identifications-isEquiv h k) encoded

    identification : h ＝ k
    identification = Fact.factor chosen

    encoding-law : ConeIdentification₁
      (cone-restrict identification J.identification-cone) encoded-cone
    encoding-law = cone-compose (pullback-factor-β encoded-cone)
      (cone-compose (cone-action-One
          (pullback-cone J.Boundary.left-map J.Boundary.right-map)
          (Fact.triangle chosen))
        (cone-compose
          (cone-restrict-assoc identification J.restriction
            (pullback-cone J.Boundary.left-map J.Boundary.right-map))
          (cone-inverse (cone-identification-restrict-One identification
            (pullback-factor-β J.identification-cone)))))

    recovery-law : ConeIdentificationEquality
      (cone-action (pullback-cone f g) identification) Φ
    recovery-law = J.Boundary.decode-into
      (cone-restrict identification J.identification-cone) Φ encoding-law

    left-image : ConeIdentification.left (cone-action (pullback-cone f g) identification) =₁ ConeIdentification.left Φ
    left-image = ConeIdentificationEquality.left recovery-law
    right-image : ConeIdentification.right (cone-action (pullback-cone f g) identification) =₁ ConeIdentification.right Φ
    right-image = ConeIdentificationEquality.right recovery-law
    matching-image :
      (ConeIdentification.compatible Φ ∙ ConeIdentificationEquality.left-boundary recovery-law) =₂
        (ConeIdentificationEquality.right-boundary recovery-law ∙
          ConeIdentification.compatible (cone-action (pullback-cone f g) identification))
    matching-image = ConeIdentificationEquality.compatible recovery-law
```


## Factors through a universal cone

A universal cone is recognized by its actual comparison with the chosen
pullback. Factoring through that equivalence supplies a vertex map and a
triangle. Pasting the complete cone betas along the triangle supplies the
complete beta of the new factor.

```agda
  pullback-reflect : {C D E T : CAT Γ} {f : MAP C E} {g : MAP D E}
    (h k : MAP T (Pullback f g))
    → ConeIdentification₁ (cone-restrict h (pullback-cone f g))
        (cone-restrict k (pullback-cone f g)) → h =₁ k
  pullback-reflect h k Φ = PullbackRecovery.identification h k (cone-identification Φ)

  pullback-factor-cong : {C D E T : CAT Γ} {f : MAP C E} {g : MAP D E}
    {s t : Cone f g T} → ConeIdentification₁ s t
    → pullback-factor s =₁ pullback-factor t
  pullback-factor-cong {s = s} {t} Φ = pullback-reflect _ _
    (cone-compose (cone-inverse (pullback-factor-β t))
      (cone-compose Φ (pullback-factor-β s)))

  pullback-factor-restrict : {C D E S T : CAT Γ} {f : MAP C E} {g : MAP D E}
    (r : MAP S T) (s : Cone f g T)
    → pullback-factor (cone-restrict r s) =₁ (pullback-factor s ∘ r)
  pullback-factor-restrict r s = pullback-reflect _ _
    (cone-compose (cone-restrict-assoc r (pullback-factor s) (pullback-cone _ _))
      (cone-compose (cone-inverse
          (cone-identification-restrict-One r (pullback-factor-β s)))
        (pullback-factor-β (cone-restrict r s))))

  IsPullback : {C D E S : CAT Γ} {f : MAP C E} {g : MAP D E}
    → Cone f g S → Set m
  IsPullback s = IsEquiv (pullback-factor s)

  module UniversalCone {C D E S : CAT Γ} {f : MAP C E} {g : MAP D E}
    (s : Cone f g S) (e : IsPullback s) where
    comparison : MAP S (Pullback f g)
    comparison = pullback-factor s

    chosen : {T : CAT Γ} (t : Cone f g T)
      → Fact.Factorization comparison (pullback-factor t)
    chosen t = Fact.factor-through-equiv e (pullback-factor t)

    factor : {T : CAT Γ} → Cone f g T → MAP T S
    factor t = Fact.factor (chosen t)

    factor-triangle : {T : CAT Γ} (t : Cone f g T)
      → (comparison ∘ factor t) =₁ pullback-factor t
    factor-triangle t = Fact.triangle (chosen t)

    β : {T : CAT Γ} (t : Cone f g T)
      → ConeIdentification₁ (cone-restrict (factor t) s) t
    β t = cone-compose (pullback-factor-β t)
      (cone-compose (cone-action-One (pullback-cone f g) (factor-triangle t))
        (cone-compose (cone-restrict-assoc (factor t) comparison (pullback-cone f g))
          (cone-inverse (cone-identification-restrict-One (factor t) (pullback-factor-β s)))))

    β₁ : {T : CAT Γ} (t : Cone f g T) → (Cone.left s ∘ factor t) =₁ Cone.left t
    β₁ t = ConeIdentification₁.left (β t)

    β₂ : {T : CAT Γ} (t : Cone f g T) → (Cone.right s ∘ factor t) =₁ Cone.right t
    β₂ t = ConeIdentification₁.right (β t)

    reflect : {T : CAT Γ} (h k : MAP T S)
      → ConeIdentification₁ (cone-restrict h s) (cone-restrict k s) → h =₁ k
    reflect h k Φ = equiv-reflect e h k (pullback-reflect _ _
      (cone-compose (cone-restrict-assoc k comparison (pullback-cone f g))
        (cone-compose (cone-inverse (cone-identification-restrict-One k (pullback-factor-β s)))
          (cone-compose Φ
            (cone-compose (cone-identification-restrict-One h (pullback-factor-β s))
              (cone-inverse (cone-restrict-assoc h comparison (pullback-cone f g))))))))
```

## Recognition by complete cone factorization

It suffices to factor the chosen pullback cone with a complete beta and reflect complete
cone identifications at the candidate vertex. The two inverse laws are
obtained by comparing the actual restricted cones, including their matchings.

```agda
  isPullback-from-factor-and-reflection : {C D E S : CAT Γ} {f : MAP C E} {g : MAP D E}
    (s : Cone f g S)
    (inverse : MAP (Pullback f g) S)
    (beta : ConeIdentification₁ (cone-restrict inverse s) (pullback-cone f g))
    (reflect : (h k : MAP S S)
      → ConeIdentification₁ (cone-restrict h s) (cone-restrict k s) → h =₁ k)
    → IsPullback s
  isPullback-from-factor-and-reflection {f = f} {g} s inverse beta reflect = record
    { inverse = inverse
    ; left-inverse-law = reflect (id _) (inverse ∘ comparison)
        (cone-compose (cone-restrict-assoc comparison inverse s)
          (cone-compose (cone-inverse (cone-identification-restrict-One comparison beta))
            (cone-compose (cone-inverse (pullback-factor-β s)) (cone-restrict-id s))))
    ; right-inverse-law = pullback-reflect (id _) (comparison ∘ inverse)
        (cone-compose (cone-restrict-assoc inverse comparison chosen-cone)
          (cone-compose (cone-inverse (cone-identification-restrict-One inverse (pullback-factor-β s)))
            (cone-compose (cone-inverse beta) (cone-restrict-id chosen-cone)))) }
    where
    chosen-cone = pullback-cone f g
    comparison = pullback-factor s
```


```agda
  pullback-recognize : {C D E S : CAT Γ} {f : MAP C E} {g : MAP D E}
    (s : Cone f g S)
    (lift : {T : CAT Γ} → Cone f g T → MAP T S)
    (beta : {T : CAT Γ} (t : Cone f g T) → ConeIdentification₁ (cone-restrict (lift t) s) t)
    (reflect : (h k : MAP S S)
      → ConeIdentification₁ (cone-restrict h s) (cone-restrict k s) → h =₁ k)
    → IsPullback s
  pullback-recognize {f = f} {g} s lift beta reflect =
    isPullback-from-factor-and-reflection s (lift (pullback-cone f g))
      (beta (pullback-cone f g)) reflect
```
