# Sections of the terminal category

The category of sections of the local terminal category is terminal.
This is the terminal case of `lem:Dependent_Product_Limits`.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.ProductFunctoriality as Action

module SCT.VolumeI.Chapter05.Section02.ProductTerminal
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (P : Products.DependentProducts W) where

private
  module S = View S
  module T = View T
module W = Weakening W
open Products.DependentProducts P
open Action W P using (reflect)

section : S.MAP S.One (Π T.One)
section = curry (T.terminate (W.cat S.One))

terminal-isEquiv : S.IsEquiv (S.terminate (Π T.One))
terminal-isEquiv = record
  { inverse = section
  ; sectionIso = reflect (T.terminal-iso _ _)
  ; retractionIso = S.terminal-iso _ _ }

terminal : S.Equiv (Π T.One) S.One
terminal = record { functor = S.terminate (Π T.One) ; isEquiv = terminal-isEquiv }
```
