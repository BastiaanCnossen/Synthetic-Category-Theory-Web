# The pullback-constructor comparison

Weakening transports both legs and the specified matching of a cone.
Preservation of the pullback constructor asserts that the factorization
of this transported cone is an equivalence. The matching is part of the
statement; preservation of an unspecified square would not suffice.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
import SCT.VolumeI.Chapter01.Section06.Cones as Cones
import SCT.VolumeI.Chapter01.Section06.PullbackData as Data

module SCT.VolumeI.Chapter05.Section01.PullbackPreservation
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (PS : Data.PullbackData S) (PT : Data.PullbackData T) where

private
  module S = View S
  module T = View T
module W = Weakening W
module SCones = Cones S
module TCones = Cones T
module PS = Data.PullbackData PS
module PT = Data.PullbackData PT

cone : {C D E X : S.CAT} {f : S.MAP C E} {g : S.MAP D E}
  → SCones.Cone f g X → TCones.Cone (W.map f) (W.map g) (W.cat X)
cone {f = f} {g} s = record
  { left = W.map (SCones.Cone.left s)
  ; right = W.map (SCones.Cone.right s)
  ; match = T._∙_ (W.comp (SCones.Cone.right s) g)
      (T._∙_ (W.term (SCones.Cone.match s)) (T._⁻¹ (W.comp (SCones.Cone.left s) f))) }

comparison : {C D E : S.CAT} (f : S.MAP C E) (g : S.MAP D E)
  → T.MAP (W.cat (PS.Pullback f g)) (PT.Pullback (W.map f) (W.map g))
comparison f g = PT.pullbackLift (cone (PS.pullbackCone f g))

record PreservesPullbacks : Set l where
  field
    comparison-isEquiv : {C D E : S.CAT} (f : S.MAP C E) (g : S.MAP D E)
      → T.IsEquiv (comparison f g)
```
