# Naturality of restriction under dependent uncurrying

The comparison with restriction is natural in the functor being
uncurried. This retains the mixed whiskering identification and the
comparison for transporting prewhiskering.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
open import SCT.VolumeI.Chapter05.Section01.Coherence using (OperationCompatibility)
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.ProductFunctoriality as Action
import SCT.VolumeI.Chapter05.Section02.ProductCalculus.ProductIdentifications as Identifications
import SCT.VolumeI.Chapter05.Section02.ProductCalculus.ProductPostcomposition as Post
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Operations as Operations
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Pairing
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as Iterated

module SCT.VolumeI.Chapter05.Section02.ProductCalculus.ProductRestrictionNaturality
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (K : OperationCompatibility W) (P : Products.DependentProducts W) where

private
  module S = View S
  module T = View T
module W = Weakening W
open Products.DependentProducts P using (Π; evaluation; uncurry)
open Action W P using (uncurry-pre)
open Identifications W K P using (action)
open Post W K P using (paste; post-square)
open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
open Calculus T
open Pairing T.vocabulary T.terminal T.products T.productLaws T.composition T.vertical T.whiskering
  using (move-square)
open Iterated T.vocabulary T.terminal T.products T.productLaws T.composition T.vertical T.whiskering T.pentagonTriangle
  using (mixed-at)

naturality : {X Y : S.CAT} {B : T.CAT} (r : S.MAP X Y)
  {h k : S.MAP Y (Π B)} (α : S._=₁_ h k)
  → T._=₂_ (uncurry-pre k r ∙ action (S._▷_ α r))
      ((action α ▷ W.map r) ∙ uncurry-pre h r)
naturality {B = B} r {h} {k} α = paste ah ak bh bk first middle last
  (post-square e (W.comp r h) (W.comp r k) (W.term (S._▷_ α r)) (W.term α ▷ W.map r)
    (Operations.pre-term-square W K r α))
  (move-square (T.comp-assoc (W.map r) (W.map k) e) last middle
    (T.comp-assoc (W.map r) (W.map h) e) (mixed-at e (W.term α) (W.map r)))
  where
  e = evaluation B
  ah = e ◁ W.comp r h
  ak = e ◁ W.comp r k
  bh = (T.comp-assoc (W.map r) (W.map h) e) ⁻¹
  bk = (T.comp-assoc (W.map r) (W.map k) e) ⁻¹
  first = action (S._▷_ α r)
  middle = e ◁ (W.term α ▷ W.map r)
  last = action α ▷ W.map r
```
