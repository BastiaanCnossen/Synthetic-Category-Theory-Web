# Arrows in a slice as squares with a constant side

Apply the functor-category pullback theorem to the endpoint presentation
of a slice. Coherent square currying, after swapping the coordinates,
identifies the resulting cospan with restriction to the constant side.
The comparison into the arrow category retains its whole pullback cone.
This is the source presentation for the slice-fibration theorem, not yet
the comparison with its directed evaluation functor.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareCurryingEquivalence as Currying
import SCT.VolumeI.Chapter01.Section06.Cospans.CospanEquivalences as Cospans
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.SplitRetractionMatching as Matching
import SCT.VolumeI.Chapter01.Section06.Cospans.FixedBaseConeAction as FixedBase

module SCT.VolumeI.Chapter04.Section03.MappingCalculus.SliceArrowSquares
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter04.Section03.MappingCalculus.EndpointSlices 𝒯 M ℱ P I public
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (Cone; ConeIso; IsPullback; conePre; module UniversalCone; pullback-comparison)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section07.FunctorPullbacks 𝒯 M ℱ P
  using (mappedCone; fun-preserves-pullback)
open import SCT.VolumeI.Chapter01.Section07.Contractible 𝒯 M ℱ using (fun-terminal-contractible)
open import SCT.VolumeI.Chapter02.Section04.ConstantDiagrams.ConstantExponential 𝒯 M ℱ
  using (constant-natural)
open import SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareCurryingCoordinates 𝒯 M ℱ
  using (coinsert)

module Endpoint (C : CAT) (u : Obj-abs [1]) (x : Obj-abs C) where
  Squares = Fun ([1] × [1]) C
  swapped : MAP Squares Squares
  swapped = funPre swap
  module Square = Currying.Family 𝒯 M ℱ swapped
    using (forward; isEquiv; module Curried)
  module Boundary = Square.Curried.Horizontal u using (comparison)

  nested : MAP Squares (Ar (Ar C))
  nested = Square.forward

  abstract
    nested-isEquiv : IsEquiv nested
    nested-isEquiv = Square.isEquiv (funPre-isEquiv swap (swap-isEquiv [1] [1]))

  coordinate : (swap ∘ coinsert u) =₁ insert u
  coordinate = pair-cong (pair-β₂ (const u) (id [1])) (pair-β₁ (const u) (id [1])) ∙
    pair-pre pr₂ pr₁ (coinsert u)

  side-comparison : (funPost (evaluate u) ∘ nested) =₁ (funPre (insert u))
  side-comparison = funPre-cong coordinate ∙ funPre-comp (coinsert u) swap ∙ Boundary.comparison

  side : MAP Squares (Ar C)
  side = funPre (insert u)
  constant-point : MAP One (Ar C)
  constant-point = identityArrow ∘ x
  category = Pullback side constant-point

  constant-endpoint : (evaluate u ∘ (funPost x ∘ constantDiagram [1] One)) =₁ x
  constant-endpoint = comp-unitʳ x ∙
    ((x ◁ evaluate-constant u) ∙ evaluate-post-at u x (constantDiagram [1] One))

  module ConstantMatching = Matching.WithRetraction.Normalize 𝒯
    (identityArrow {C}) (evaluate u) (evaluate-constant u)
    (constant-natural [1] x) constant-endpoint
    using (matching; image-law)

  abstract
    constant-isEquiv : IsEquiv (constantDiagram [1] One)
    constant-isEquiv = equiv-cancel-left (constantDiagram [1] One) (terminate (Ar One))
      (fun-terminal-contractible [1])
      (equiv-transport (terminal-iso (id One) (terminate (Ar One) ∘ constantDiagram [1] One))
        (id-isEquiv One))

  change : CospanMap side constant-point (funPost (evaluate u)) (funPost x)
  change = record
    { left = nested ; right = constantDiagram [1] One ; base = id (Ar C)
    ; leftSquare = (comp-unitˡ side) ⁻¹ ∙ side-comparison
    ; rightSquare = (comp-unitˡ constant-point) ⁻¹ ∙ ConstantMatching.matching }
  module Change = CospanMap change using (mapCone)
  module Fixed = FixedBase.Fixed 𝒯 P nested (constantDiagram [1] One)
    side-comparison ConstantMatching.matching using (module At)
  module Equivalent = Cospans.CospanEquivalence 𝒯 P change nested-isEquiv constant-isEquiv (id-isEquiv (Ar C))
    using (pullbackMap-isEquiv)

  module ToArrows {T : CAT} (s : Cone (evaluate u) x T) (es : IsPullback s) where
    mapped = mappedCone [1] s
    abstract
      mapped-isPullback : IsPullback mapped
      mapped-isPullback = fun-preserves-pullback [1] s es
    image = Change.mapCone (pullbackCone side constant-point)
    module Target = UniversalCone mapped mapped-isPullback using (factor; factor-β)

    forward : MAP category (Ar T)
    forward = Target.factor image

    comparison : ConeIso (conePre forward mapped) image
    comparison = Target.factor-β image

    isEquiv : IsEquiv forward
    isEquiv = pullback-comparison image mapped forward comparison
      Equivalent.pullbackMap-isEquiv mapped-isPullback

module SliceAt {C : CAT} (x : Obj-abs C) where
  module Input = SliceEndpoint x using (square; square-isPullback)
  module Presentation = Endpoint C one x using (module ToArrows)
  open Presentation.ToArrows Input.square Input.square-isPullback public

module CosliceAt {C : CAT} (x : Obj-abs C) where
  module Input = CosliceEndpoint x using (square; square-isPullback)
  module Presentation = Endpoint C zero x using (module ToArrows)
  open Presentation.ToArrows Input.square Input.square-isPullback public
```
