# The empty anima context

The generic point is a functor from the local terminal category to the
weakening of the empty category. Preservation of the initial category
and its strictness imply that every local category is terminal. The sum
is empty and the dependent product is terminal, as in the second exercise.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Initial as Initial
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section02.DependentEquivalences as Equivalences
import SCT.VolumeI.Chapter05.Section02.ProductFunctoriality as ProductAction
import SCT.VolumeI.Chapter05.Section02.ProductTerminal as ProductTerminal
import SCT.VolumeI.Chapter05.Section03.GenericPoint as Point

module SCT.VolumeI.Chapter05.Section05.EmptyContext
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (MS : Mapping.MappingAnimae S) (MT : Mapping.MappingAnimae T)
  (IS : Initial.InitialStructure S MS) (IT : Initial.InitialStructure T MT)
  (SS : Initial.StrictInitial S MS IS) (ST : Initial.StrictInitial T MT IT)
  (P : Products.DependentProducts W) (Q : Sums.DependentSums W P)
  (zero-anima : View.isAn S (Initial.InitialStructure.Zero IS))
  (e : View.Equiv S (Sums.DependentSums.Σ Q (View.One T)) (Initial.InitialStructure.Zero IS))
  (initial-comparison : View.Equiv T (Weakening.cat W (Initial.InitialStructure.Zero IS))
    (Initial.InitialStructure.Zero IT)) where

private
  module S = View S
  module T = View T
  A : S.AN
  A = record { category = Initial.InitialStructure.Zero IS ; witness = zero-anima }
module W = Weakening W
module P = Products.DependentProducts P
module Q = Sums.DependentSums Q
module SS = Initial.StrictInitial SS
module ST = Initial.StrictInitial ST
module G = Point W P Q A e using (generic; projection)
module E = Equivalences W P using (Π-map-isEquiv)
module PA = ProductAction W P using (Π-map)

terminal-to-empty : T.MAP T.One (Initial.InitialStructure.Zero IT)
terminal-to-empty = T._∘_ (T.Equiv.functor initial-comparison) G.generic

local-terminal : (B : T.CAT) → T.IsEquiv (T.terminate B)
local-terminal B = T.equiv-cancel-left (T.terminate B) terminal-to-empty
  (ST.into-zero-isEquiv terminal-to-empty)
  (ST.into-zero-isEquiv (T._∘_ terminal-to-empty (T.terminate B)))

sum-empty : (B : T.CAT) → S.IsEquiv (G.projection B)
sum-empty B = SS.into-zero-isEquiv (G.projection B)

product-terminal : (B : T.CAT) → S.IsEquiv (S.terminate (P.Π B))
product-terminal B = S.equiv-transport (S.terminal-iso _ _)
  (S.equiv-compose (PA.Π-map (T.terminate B)) (S.terminate (P.Π T.One))
    (E.Π-map-isEquiv (local-terminal B)) (ProductTerminal.terminal-isEquiv W P))
```
