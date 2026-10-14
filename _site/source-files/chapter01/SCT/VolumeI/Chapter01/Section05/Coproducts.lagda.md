# Coproducts of categories

A coproduct has two inclusions. Its universal property says that restriction
to these inclusions is an equivalence of mapping animae. The restriction
functor is the actual pair of precomposition functors; copairing and its
comparison laws will be derived from its chosen inverse.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section05.Coproducts where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_⊔_)
open Operations
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae using (Map)
open import SCT.VolumeI.Chapter01.Section04.Functoriality using (mapPre)

module _ {Γ : Context} where
  infixr 5 _⊔_

  postulate
    _⊔_ : CAT Γ → CAT Γ → CAT Γ
    in₁ : {C D : CAT Γ} → MAP C (C ⊔ D)
    in₂ : {C D : CAT Γ} → MAP D (C ⊔ D)

  coproductRestriction : (C D E : CAT Γ)
    → MAP (Map (C ⊔ D) E) (Map C E × Map D E)
  coproductRestriction C D E = pair (mapPre in₁) (mapPre in₂)

  postulate
    coproductRestriction-isEquiv : (C D E : CAT Γ)
      → IsEquiv (coproductRestriction C D E)
```
