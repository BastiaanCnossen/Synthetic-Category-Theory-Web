# The coproduct axiom

The restriction functor is constructed from the two inclusions using the
precomposition functors already defined in Section 1.3. Only the equivalence
of this particular functor is assumed (`post:Coproduct_Of_Categories`).

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level) renaming (_⊔_ to _⊔ℓ_)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Setup as Setup

module SCT.VolumeI.Chapter01.Section04.Coproducts
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯 M

record CoproductData : Set (c ⊔ℓ m ⊔ℓ a) where
  infixr 5 _⊔_
  field
    _⊔_ : CAT → CAT → CAT
    in₁ : {C D : CAT} → MAP C (C ⊔ D)
    in₂ : {C D : CAT} → MAP D (C ⊔ D)
    coproduct-isAn : {C D : CAT} → isAn C → isAn D → isAn (C ⊔ D)

  coproductRestriction : (C D E : CAT) → MAP (Map (C ⊔ D) E) (Map C E × Map D E)
  coproductRestriction C D E = pair (mapPre in₁) (mapPre in₂)

record CoproductLaws (B : CoproductData) : Set (c ⊔ℓ m) where
  open CoproductData B
  field
    coproductRestriction-isEquiv : (C D E : CAT) → IsEquiv (coproductRestriction C D E)

record CoproductStructure : Set (c ⊔ℓ m ⊔ℓ a) where
  field
    dataCoproduct : CoproductData
    lawsCoproduct : CoproductLaws dataCoproduct
  open CoproductData dataCoproduct public
  open CoproductLaws lawsCoproduct public
```
