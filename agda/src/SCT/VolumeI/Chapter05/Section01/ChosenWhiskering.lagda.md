# The selected whiskering laws

Each whiskering law receives a comparison after its functor and identification boundaries have been adjusted. The parameterized equations retain the chosen witnesses of the source and target theories.

```agda
{-# OPTIONS --safe --without-K #-}
module SCT.VolumeI.Chapter05.Section01.ChosenWhiskering where
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
open import SCT.VolumeI.Chapter05.Section01.Coherence
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.WhiskeringLawBoundary as Boundary

record ChosenWhiskering {l : Level} {S T : Theory l l l}
  (W : Weakening S T) (K : OperationCompatibility W) : Set l where
  private
    module S = View S
    module T = View T
    module B = Boundary W K
  open Weakening W using (map)
  field
    post-identity : {C D E : S.CAT} (u : S.MAP D E) (f : S.MAP C D)
      → T._=₃_ (B.PostIdentity.transported u f) (T.postWhisker-idIso (map u) (map f))
    pre-identity : {B C D : S.CAT} (f : S.MAP C D) (k : S.MAP B C)
      → T._=₃_ (B.PreIdentity.transported f k) (T.preWhisker-idIso (map f) (map k))
    post-vertical : {C D E : S.CAT} (f g h : S.MAP C D) (u : S.MAP D E)
      → B.PostVertical.Law.Preserves f g h u (S.postWhisker-isoComp f g h u) (B.PostVertical.target f g h u)
    pre-vertical : {B C D : S.CAT} (f g h : S.MAP C D) (k : S.MAP B C)
      → B.PreVertical.Law.Preserves f g h k (S.preWhisker-isoComp f g h k) (B.PreVertical.target f g h k)
    fixed-outer : {B C D : S.CAT} (F G : S.MAP C D) (h k : S.MAP B C) (tau : S._=₁_ F G)
      → B.FixedOuter.Law.Preserves F G h k tau (S.interchange-fixedOuter F G h k tau) (B.FixedOuter.target F G h k tau)
    fixed-inner : {B C D : S.CAT} (F G : S.MAP C D) (h k : S.MAP B C) (sigma : S._=₁_ h k)
      → B.FixedInner.Law.Preserves F G h k sigma (S.interchange-fixedInner F G h k sigma) (B.FixedInner.target F G h k sigma)
```
