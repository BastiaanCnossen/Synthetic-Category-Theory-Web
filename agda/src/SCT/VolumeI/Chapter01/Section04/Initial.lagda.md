# The initial category

The axiom `post:Initial_Category` says that the mapping anima out of the
chosen initial anima is contractible. The map out and its uniqueness below
are consequences, obtained by naming and decoding functors.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Setup as Setup

module SCT.VolumeI.Chapter01.Section04.Initial
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯 M

record InitialStructure : Set (c ⊔ m ⊔ a) where
  field
    Zero : CAT
    zero-isAn : isAn Zero
    maps-from-zero-contractible : (C : CAT) → IsContractible (Map Zero C)

contractible-source : {C D : CAT} (f : MAP C D)
  → IsEquiv f → IsContractible D → IsContractible C
contractible-source {C} {D} f e h = equiv-transport
  (terminal-iso (terminate D ∘ f) (terminate C))
  (equiv-compose f (terminate D) e h)

contractible-iso : {C X : CAT} → IsContractible C
  → (f g : MAP X C) → IsContractible (f ＝ g)
contractible-iso {C} e f g = contractible-source (postWhisker (terminate C))
  (postWhisker-isEquiv (terminate C) e f g)
  (terminalIso-isEquiv (terminate C ∘ f) (terminate C ∘ g))

contractible-compare : {C X : CAT} → IsContractible C
  → (f g : MAP X C) → =₁ f g
contractible-compare {C} e f g = equiv-reflect e f g (terminal-iso _ _)

module Initiality (I : InitialStructure) where
  open InitialStructure I public

  initiate : (C : CAT) → MAP Zero C
  initiate C = decodeMap (IsEquiv.inverse (maps-from-zero-contractible C))

  initialIso-contractible : {C : CAT} (f g : MAP Zero C)
    → IsContractible (f ＝ g)
  initialIso-contractible {C} f g = contractible-source (nameMap-isoMap f g)
    (nameMap-isoMap-isEquiv f g)
    (contractible-iso (maps-from-zero-contractible C) (nameMap f) (nameMap g))

  initial-iso : {C : CAT} (f g : MAP Zero C) → =₁ f g
  initial-iso f g = IsEquiv.inverse (initialIso-contractible f g)

  initial-Iso₂ : {C : CAT} {f g : MAP Zero C} (α β : =₁ f g) → =₂ α β
  initial-Iso₂ {f = f} {g} = contractible-compare (initialIso-contractible f g)
```

Strictness is a separate axiom, `axiom:Mapping_Into_Empty_Category`. The
product-with-empty lemma follows by applying it to the second projection.

```agda
record StrictInitial (I : InitialStructure) : Set (c ⊔ m) where
  open InitialStructure I
  field
    into-zero-isEquiv : {C : CAT} (f : MAP C Zero) → IsEquiv f

module Strictness (I : InitialStructure) (S : StrictInitial I) where
  open InitialStructure I
  open StrictInitial S

  product-zero-isEquiv : (C : CAT) → IsEquiv (pr₂ {C} {Zero})
  product-zero-isEquiv C = into-zero-isEquiv pr₂
```
