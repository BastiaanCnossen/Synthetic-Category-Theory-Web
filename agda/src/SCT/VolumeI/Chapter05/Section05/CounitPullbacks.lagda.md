# The counit squares are pullbacks

For constant families, the counit and the base projection exhibit the
total category as a product. Paste a counit naturality square with this
product square over the terminal category. Naturality of the base
projection identifies the outer square with the corresponding product
square for the source.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
import SCT.VolumeI.Chapter05.Section01.Products as WeakProducts
import SCT.VolumeI.Chapter05.Section01.FunctorPreservation as Preservation
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section03.ProductConstructions as ProductMaps
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Functors
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.PullbackSquares as Squares
import SCT.VolumeI.Chapter01.Section06.PullbackProducts as PullbackProducts
import SCT.VolumeI.Chapter01.Section06.PastingLemma as Pasting
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section02.SumFunctoriality as SumAction
import SCT.VolumeI.Chapter05.Section03.GenericPoint as Point
import SCT.VolumeI.Chapter05.Section03.ConstantFamilies as Constants

module SCT.VolumeI.Chapter05.Section05.CounitPullbacks
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (WP : WeakProducts.PreservesProducts W)
  (MS : Mapping.MappingAnimae S) (MT : Mapping.MappingAnimae T)
  (FS : Functors.FunctorCategories S MS) (FT : Functors.FunctorCategories T MT)
  (K : Preservation.FunctorComparison W MS MT FS FT)
  (P : Products.DependentProducts W) (Q : Sums.DependentSums W P)
  (A : View.AN S) (e : View.Equiv S (Sums.DependentSums.Σ Q (View.One T)) (View.AN.category {T = S} A))
  (PB : Pullbacks.PullbackStructure S) where

private
  module S = View S
  module T = View T
module W = Weakening W
module Q = Sums.DependentSums Q
module QA = SumAction W P Q using (Σ-map; counit; counit-natural)
module G = Point W P Q A e using (base; projection; projection-natural)
open S using (_∘_; _◁_; _▷_; _⁻¹)
open Calculus S using (_then_; pair-pre; pair-cong)
open Pullbacks.PullbackStructure PB
open Squares S PB using (Cone; IsPullback; pullback-cone-invariant)
open PullbackProducts S PB using (module TerminalBase; coneIso-over-One)
open ProductMaps S.vocabulary S.terminal S.products S.productLaws S.composition using (swap; swap-isEquiv)

module ProductSquare (C : S.CAT) (f : S.MAP C S.One) where
  module Known = TerminalBase f (S.terminate G.base)
  module Constant = Constants W WP MS MT FS FT K P Q A e C
    using (comparison; comparison-isEquiv)

  square : Cone f (S.terminate G.base) (Q.Σ (W.cat C))
  square = record { left = QA.counit C ; right = G.projection (W.cat C) ; match = S.terminal-iso _ _ }

  pair-isEquiv : S.IsEquiv (S.pair (QA.counit C) (G.projection (W.cat C)))
  pair-isEquiv = S.equiv-transport
    (pair-pre S.pr₂ S.pr₁ Constant.comparison then
      pair-cong (S.pair-β₂ (G.projection (W.cat C)) (QA.counit C))
        (S.pair-β₁ (G.projection (W.cat C)) (QA.counit C)))
    (S.equiv-compose Constant.comparison swap Constant.comparison-isEquiv (swap-isEquiv G.base C))

  square-isPullback : IsPullback square
  square-isPullback = S.equiv-cancel-left (pullbackLift square) Known.toProduct Known.toProduct-isEquiv
    (S.equiv-transport ((pair-pre pullback₁ pullback₂ (pullbackLift square) then
      pair-cong (pullbackLift-β₁ square) (pullbackLift-β₂ square)) ⁻¹) pair-isEquiv)

module Naturality {C D : S.CAT} (f : S.MAP C D) where
  module Right = ProductSquare D (S.terminate D)
  module Outer = ProductSquare C (S.terminate D ∘ f)
  module Paste = Pasting.Pasting S PB f (S.terminate D) (S.terminate G.base)
    Right.square Right.square-isPullback

  square : Cone f (QA.counit D) (Q.Σ (W.cat C))
  square = record { left = QA.counit C ; right = QA.Σ-map (W.map f) ; match = (QA.counit-natural f) ⁻¹ }

  square-isPullback : IsPullback square
  square-isPullback = Paste.cancel-isPullback square
    (pullback-cone-invariant (coneIso-over-One Outer.square (Paste.Paste.flatten square)
      (S.idIso (QA.counit C)) ((G.projection-natural (W.map f)) ⁻¹)) Outer.square-isPullback)
```
