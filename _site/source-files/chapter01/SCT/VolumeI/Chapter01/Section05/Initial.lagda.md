# The initial category

Initiality says that the mapping anima from Zero to any category is
contractible. Decoding its chosen point gives the initiation functor.
The actual naming equivalence transfers contractibility to the identification
anima between any two functors from Zero.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section05.Initial where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions using (IsContractible)
open import SCT.VolumeI.Chapter01.Section03.Equivalences
  using (contractible-source; contractible-unique)
open import SCT.VolumeI.Chapter01.Section03.WhiskeringEquivalence
  using (contractible-identifications)
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae using (Map)
open import SCT.VolumeI.Chapter01.Section04.Points
  using (name; decode; name⁼-functor; name⁼-isEquiv)

module _ {Γ : Context} where
  postulate
    Zero : CAT Γ
    maps-from-zero-contractible : (C : CAT Γ) → IsContractible (Map Zero C)

  initiate : (C : CAT Γ) → MAP Zero C
  initiate C = decode (IsEquiv.inverse (maps-from-zero-contractible C))

  initial-identifications-contractible : {C : CAT Γ} (f g : MAP Zero C)
    → IsContractible (Equal f g)
  initial-identifications-contractible {C} f g =
    contractible-source (name⁼-functor f g) (name⁼-isEquiv f g)
      (contractible-identifications (maps-from-zero-contractible C) (name f) (name g))

  initial-unique : {C : CAT Γ} (f g : MAP Zero C) → f =₁ g
  initial-unique f g = IsEquiv.inverse (initial-identifications-contractible f g)
```

The identification anima is contractible, so two identification families
with any common categorical parameter are identified. The parameter need
not be an anima. At One this is uniqueness of individual identifications.

```agda
  module _ {A : CAT Γ} where
    open Terms.Equalities A using (_＝_)

    initial-unique₂ : {C : CAT Γ} {f g : MAP Zero C}
      (α β : f ＝ g) → α =₁ β
    initial-unique₂ {f = f} {g} =
      contractible-unique (initial-identifications-contractible f g)
```

## Strictness

Strictness is a separate assumption: every functor into Zero is an
equivalence. Applied to the second projection, it gives the product
consequence below. Initiality and its uniqueness results do not use it.
No assumption that Zero is an anima is made.

```agda
module _ {Γ : Context} where
  postulate
    into-zero-isEquiv : {C : CAT Γ} (f : MAP C Zero) → IsEquiv f

  product-zero-isEquiv : (C : CAT Γ) → IsEquiv (pr₂ {C = C} {D = Zero})
  product-zero-isEquiv C = into-zero-isEquiv pr₂
```
