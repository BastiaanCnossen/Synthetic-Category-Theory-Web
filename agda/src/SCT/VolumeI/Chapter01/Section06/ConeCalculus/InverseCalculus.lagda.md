# Inverting matching isomorphisms

Reversing a cone uses the inverse identities proved in
`Section03.IdentificationCalculus.Inverses`. This module specializes that
library to the common theory parameter; it preserves the chosen witnesses.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Inverses as Inverses

module SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus
  {c m a : Level} (𝒯 : Theory c m a) where

open Theory 𝒯
open Inverses vocabulary terminal products productLaws composition vertical public
  using (isoInverse-unique; inverse-identity; inverse-inverse; inverse-composite)
open Inverses.Whiskering vocabulary terminal products productLaws composition vertical whiskering public
  using (pre-inverse)
```
