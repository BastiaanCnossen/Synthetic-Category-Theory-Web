# The terminal category

This is the supplied structure of `post:Terminal_Category`, in any ambient
anima context. `One` was introduced with the vocabulary so that absolute
objects and natural isomorphisms could be defined before universal properties.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section01.Terminal where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary

module _ {Γ : Context} where
  postulate
    terminate : (C : CAT Γ) → MAP C One
    terminal-identifications-isEquiv : {T : CAT Γ} (f g : MAP T One)
      → IsEquiv (terminate (f ＝ g))

module Constructions where
  module _ {Γ : Context} where
    terminal-identification : {P : CAT Γ} (f g : MAP P One) → f =₁ g
    terminal-identification f g = IsEquiv.inverse (terminal-identifications-isEquiv f g)

    IsContractible : CAT Γ → Set m
    IsContractible C = IsEquiv (terminate C)

    const : {P C : CAT Γ} → Obj-abs C → MAP P C
    const {P} x = x ∘ terminate P
```

`terminal-identification` is a proved construction: the inverse supplied by the terminal
axiom is precisely a functor from `One` to the required isomorphism anima.

## Contractibility and contractions

A contraction specifies its center and its identification with the identity.
The following constructions translate between this datum and contractibility;
no uniqueness of the witness records is assumed.

```agda
module Contractibility where
  open Constructions

  module _ {Γ : Context} where
    record Contraction (C : CAT Γ) : Set m where
      field
        center : Obj-abs C
        contraction : (id C) =₁ (const center)

    contractible-to-contraction : {C : CAT Γ} → IsContractible C → Contraction C
    contractible-to-contraction e = record
      { center = IsEquiv.inverse e
      ; contraction = IsEquiv.left-inverse-law e
      }

    contraction-to-contractible : {C : CAT Γ} → Contraction C → IsContractible C
    contraction-to-contractible {C} H = record
      { inverse = Contraction.center H
      ; left-inverse-law = Contraction.contraction H
      ; right-inverse-law = terminal-identification (id One) (terminate C ∘ Contraction.center H)
      }

    terminal-identifications-contractible : {X : CAT Γ} (f g : MAP X One) → IsContractible (f ＝ g)
    terminal-identifications-contractible = terminal-identifications-isEquiv
```
