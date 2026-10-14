# Elementary pullback constructions

Base change preserves equivalences. The proof factors the inverse cone and
uses recovery of a cone identification from one leg when the opposite
cospan arrow is an equivalence. Recovery retains the prescribed image and
the complete matching square.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.PullbackConstructions where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-unitʳ; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Products
open Calculus
open import SCT.VolumeI.Chapter01.Section03.Equivalences
import SCT.VolumeI.Chapter01.Section03.Factorizations as Fact
open import SCT.VolumeI.Chapter01.Section03.WhiskeringEquivalence using (factor-through-postWhisker)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
open import SCT.VolumeI.Chapter01.Section06.ConeTransport
open import SCT.VolumeI.Chapter01.Section06.ConeUniversality
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares

module _ {Γ : Context} where
  module _ {X C D E T : CAT Γ} {f : MAP C E} {g : MAP D E} where
    open Terms.Equalities X using (_＝_)

    module RightLegRecovery (eg : IsEquiv g) (s t : Cone f g T)
      (α : Cone.left s ＝ Cone.left t) where
      private
        τ = const {P = X} (Cone.match s)
        boundary = const (Cone.match t) ∙ (f ◁ α)
        chosen : Fact.Factorization (postWhisker g) (boundary ∙ τ ⁻¹)
        chosen = factor-through-postWhisker g eg (boundary ∙ τ ⁻¹)

      right : Cone.right s ＝ Cone.right t
      right = Fact.factor chosen

      right-image : (g ◁ right) =₁ (boundary ∙ τ ⁻¹)
      right-image = Fact.triangle chosen

      identification : ConeIdentification X s t
      identification = record
        { left = α; right = right
        ; compatible = comp₌-cong (right-image ⁻¹) (id₌ τ) ∙
            (inv-comp-right boundary τ) ⁻¹ }

  module _ {X C D E T : CAT Γ} {f : MAP C E} {g : MAP D E} where
    open Terms.Equalities X using (_＝_)

    cone-identification-from-left : IsEquiv g → (s t : Cone f g T)
      → Cone.left s ＝ Cone.left t → ConeIdentification X s t
    cone-identification-from-left = RightLegRecovery.identification

  cone-identification-from-left-One : {C D E T : CAT Γ} {f : MAP C E} {g : MAP D E}
    → IsEquiv g → (s t : Cone f g T)
    → Cone.left s =₁ Cone.left t → ConeIdentification₁ s t
  cone-identification-from-left-One eg s t α = cone-identification-One
    (RightLegRecovery.identification eg s t α)

  cone-identification-over-One : {C D T : CAT Γ} {f : MAP C One} {g : MAP D One}
    (s t : Cone f g T) → Cone.left s =₁ Cone.left t
    → Cone.right s =₁ Cone.right t → ConeIdentification₁ s t
  cone-identification-over-One s t α β = record
    { left = α; right = β; compatible = terminal-unique₂ _ _ }
```

## Base change of an equivalence

Factoring f through the equivalence g supplies a cone with identity left leg.
Its pullback factor is an inverse to the first projection. The other inverse
law follows by reflecting the complete cone identification supplied above.

```agda
  module BaseChangeEquivalence {C D E : CAT Γ} (f : MAP C E) (g : MAP D E)
    (eg : IsEquiv g) where
    private
      chosen = Fact.factor-through-equiv eg f

    inverse-cone : Cone f g C
    inverse-cone = record
      { left = id C; right = Fact.factor chosen
      ; match = (Fact.triangle chosen) ⁻¹ ∙ comp-unitʳ f }

    inverse : MAP C (Pullback f g)
    inverse = pullback-factor inverse-cone

    projection-inverse : (pullback₁ ∘ inverse) =₁ id C
    projection-inverse = pullback-factor-β₁ inverse-cone

    inverse-projection : (inverse ∘ pullback₁) =₁ id (Pullback f g)
    inverse-projection = pullback-reflect _ _
      (cone-identification-from-left-One eg _ _
        ((comp-unitʳ pullback₁) ⁻¹ ∙
          (comp-unitˡ pullback₁ ∙
            ((projection-inverse ▷ pullback₁) ∙ (comp-assoc pullback₁ inverse pullback₁) ⁻¹))))

    projection-isEquiv : IsEquiv (pullback₁ {f = f} {g = g})
    projection-isEquiv = record
      { inverse = inverse
      ; left-inverse-law = inverse-projection ⁻¹
      ; right-inverse-law = projection-inverse ⁻¹ }

  pullback₁-isEquiv : {C D E : CAT Γ} (f : MAP C E) (g : MAP D E)
    → IsEquiv g → IsEquiv (pullback₁ {f = f} {g = g})
  pullback₁-isEquiv = BaseChangeEquivalence.projection-isEquiv

  isPullback-from-left-isEquiv : {C D E T : CAT Γ} {f : MAP C E} {g : MAP D E}
    → IsEquiv g → (s : Cone f g T) → IsEquiv (Cone.left s) → IsPullback s
  isPullback-from-left-isEquiv {f = f} {g} eg s es =
    equiv-cancel-left (pullback-factor s) pullback₁ (pullback₁-isEquiv f g eg)
      (equiv-transport ((pullback-factor-β₁ s) ⁻¹) es)

  left-isEquiv-from-isPullback : {C D E T : CAT Γ} {f : MAP C E} {g : MAP D E}
    → IsEquiv g → (s : Cone f g T) → IsPullback s → IsEquiv (Cone.left s)
  left-isEquiv-from-isPullback {f = f} {g} eg s es = equiv-transport (pullback-factor-β₁ s)
    (equiv-compose (pullback-factor s) pullback₁ es (pullback₁-isEquiv f g eg))
```

## Chosen symmetry and units

The chosen pullback cone is universal: its factor agrees with the identity
by full cone reflection. General symmetry of universal cones therefore
makes its chosen swap map an equivalence. This chooses the inverse supplied
by recognition, rather than selecting the reverse swap as in the first
rebuild. The explicit double-swap equation below remains available; no
equality of the two equivalence witnesses is asserted.

```agda
  pullback-cone-isPullback : {C D E : CAT Γ} (f : MAP C E) (g : MAP D E)
    → IsPullback (pullback-cone f g)
  pullback-cone-isPullback f g = equiv-transport
    ((pullback-reflect _ _
      (cone-compose (cone-inverse (cone-restrict-id (pullback-cone f g)))
        (pullback-factor-β (pullback-cone f g)))) ⁻¹)
    (id-isEquiv (Pullback f g))

  pullback-swap : {C D E : CAT Γ} (f : MAP C E) (g : MAP D E)
    → MAP (Pullback f g) (Pullback g f)
  pullback-swap f g = pullback-factor (cone-swap (pullback-cone f g))

  pullback-swap-isEquiv : {C D E : CAT Γ} (f : MAP C E) (g : MAP D E)
    → IsEquiv (pullback-swap f g)
  pullback-swap-isEquiv f g = SwappedCone.isPullback (pullback-cone f g) (pullback-cone-isPullback f g)

  pullback₂-isEquiv : {C D E : CAT Γ} (f : MAP C E) (g : MAP D E)
    → IsEquiv f → IsEquiv (pullback₂ {f = f} {g = g})
  pullback₂-isEquiv f g ef = equiv-transport (pullback-factor-β₁ (cone-swap (pullback-cone f g)))
    (equiv-compose (pullback-swap f g) pullback₁ (pullback-swap-isEquiv f g) (pullback₁-isEquiv g f ef))

  pullback-unitˡ : {C E : CAT Γ} (f : MAP C E)
    → IsEquiv (pullback₁ {f = f} {g = id E})
  pullback-unitˡ {E = E} f = pullback₁-isEquiv f (id E) (id-isEquiv E)

  pullback-unitʳ : {C E : CAT Γ} (f : MAP C E)
    → IsEquiv (pullback₂ {f = id E} {g = f})
  pullback-unitʳ {E = E} f = pullback₂-isEquiv (id E) f (id-isEquiv E)
```

## Computation of symmetry

The double swap and the swap of a factor retain their full cone comparisons.

```agda
  pullback-swap-swap : {C D E : CAT Γ} (f : MAP C E) (g : MAP D E) →
    (pullback-swap g f ∘ pullback-swap f g) =₁ (id (Pullback f g))
  pullback-swap-swap f g = pullback-reflect _ _
    (cone-compose (cone-inverse (cone-restrict-id (pullback-cone f g)))
      (cone-compose (cone-swap-twice (pullback-cone f g))
      (cone-compose (cone-swap-identification (pullback-factor-β (cone-swap (pullback-cone f g))))
      (cone-compose (cone-swap-restrict (pullback-swap f g) (pullback-cone g f))
      (cone-compose (cone-identification-restrict-One (pullback-swap f g) (pullback-factor-β (cone-swap (pullback-cone g f))))
        (cone-inverse (cone-restrict-assoc (pullback-swap f g) (pullback-swap g f) (pullback-cone f g))))))))

  pullback-factor-swap : {C D E T : CAT Γ} {f : MAP C E} {g : MAP D E}
    (s : Cone f g T) → (pullback-factor (cone-swap s)) =₁ (pullback-swap f g ∘ pullback-factor s)
  pullback-factor-swap {f = f} {g} s = pullback-reflect _ _
    (cone-compose (cone-inverse swapped-factor-law) (pullback-factor-β (cone-swap s)))
    where
    swapped-factor-law : ConeIdentification₁
      (cone-restrict (pullback-swap f g ∘ pullback-factor s) (pullback-cone g f)) (cone-swap s)
    swapped-factor-law = cone-compose (cone-swap-identification (pullback-factor-β s))
      (cone-compose (cone-swap-restrict (pullback-factor s) (pullback-cone f g))
      (cone-compose (cone-identification-restrict-One (pullback-factor s) (pullback-factor-β (cone-swap (pullback-cone f g))))
        (cone-inverse (cone-restrict-assoc (pullback-factor s) (pullback-swap f g) (pullback-cone g f)))))

```

## Terminal base and products

The product and swapped product presentations retain their actual maps,
inverse witnesses and the swapped-coordinate beta laws.

```agda
module _ {Γ : Context} where
  module TerminalBase {C D : CAT Γ} (f : MAP C One) (g : MAP D One) where

    product-cone : Cone f g (C × D)
    product-cone = record { left = pr₁ ; right = pr₂ ; match = terminal-identification _ _ }

    to-product : MAP (Pullback f g) (C × D)
    to-product = pair pullback₁ pullback₂

    from-product : MAP (C × D) (Pullback f g)
    from-product = pullback-factor product-cone

    to-from : (to-product ∘ from-product) =₁ (id (C × D))
    to-from = pair-projections ∙
      (pair⁼ (pullback-factor-β₁ product-cone) (pullback-factor-β₂ product-cone) ∙ pair-pre pullback₁ pullback₂ from-product)

    from-to : (from-product ∘ to-product) =₁ (id (Pullback f g))
    from-to = pullback-reflect _ _ (cone-identification-over-One _ _
      ((comp-unitʳ pullback₁) ⁻¹ ∙
        (pair-β₁ pullback₁ pullback₂ ∙ ((pullback-factor-β₁ product-cone ▷ to-product) ∙
          (comp-assoc to-product from-product pullback₁) ⁻¹)))
      ((comp-unitʳ pullback₂) ⁻¹ ∙
        (pair-β₂ pullback₁ pullback₂ ∙ ((pullback-factor-β₂ product-cone ▷ to-product) ∙
          (comp-assoc to-product from-product pullback₂) ⁻¹))))

    to-product-isEquiv : IsEquiv to-product
    to-product-isEquiv = record
      { inverse = from-product ; left-inverse-law = from-to ⁻¹ ; right-inverse-law = to-from ⁻¹ }

    product-cone-isPullback : IsPullback product-cone
    product-cone-isPullback = record
      { inverse = to-product ; left-inverse-law = to-from ⁻¹ ; right-inverse-law = from-to ⁻¹ }

    to-swapped : MAP (Pullback f g) (D × C)
    to-swapped = pair pullback₂ pullback₁

    from-swapped : MAP (D × C) (Pullback f g)
    from-swapped = from-product ∘ swap {C = D} {D = C}

    to-swapped-isEquiv : IsEquiv to-swapped
    to-swapped-isEquiv = equiv-transport
      (pair⁼ (pair-β₂ pullback₁ pullback₂) (pair-β₁ pullback₁ pullback₂) ∙ pair-pre pr₂ pr₁ to-product)
      (equiv-compose to-product (swap {C = C} {D = D}) to-product-isEquiv (swap-isEquiv C D))

    from-swapped-isEquiv : IsEquiv from-swapped
    from-swapped-isEquiv = equiv-compose (swap {C = D} {D = C}) from-product (swap-isEquiv D C) product-cone-isPullback

    from-swapped-β₁ : (pullback₁ ∘ from-swapped) =₁ (pr₂ {C = D} {D = C})
    from-swapped-β₁ = pair-β₁ pr₂ pr₁ ∙
      ((pullback-factor-β₁ product-cone ▷ swap {C = D} {D = C}) ∙ (comp-assoc (swap {C = D} {D = C}) from-product pullback₁) ⁻¹)

    from-swapped-β₂ : (pullback₂ ∘ from-swapped) =₁ (pr₁ {C = D} {D = C})
    from-swapped-β₂ = pair-β₂ pr₂ pr₁ ∙
      ((pullback-factor-β₂ product-cone ▷ swap {C = D} {D = C}) ∙ (comp-assoc (swap {C = D} {D = C}) from-product pullback₂) ⁻¹)
  module PullbackProduct (C D : CAT Γ) = TerminalBase (terminate C) (terminate D)
```
