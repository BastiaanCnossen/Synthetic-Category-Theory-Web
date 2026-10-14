# Comparing universal and parameterwise coherence

The internal comparisons are normalized restrictions of the comparisons
on the universal mapping-anima parameters. We compare them with the
retained-route comparisons lifted directly at the parameter in question.
The change-of-parameter calculus is reexported from
`UniversalCoherenceCalculus`.

The associator calculation pastes the four composition squares and the
external associativity square, then cancels the fixed endpoint comparison.
The explicit reflection step uses both product projections.
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Substitution.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as MappingAnimae
import SCT.VolumeI.Chapter01.Section04.Currying as Currying
import SCT.VolumeI.Chapter01.Section04.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.InternalCoherence as InternalCoherence
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.RetainedComparisonLaws as RetainedComparisonLaws
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.InternalPentagon as InternalPentagon
import SCT.VolumeI.Chapter01.Section04.Substitution.ParameterChange as ParameterChange
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.CompositionNaturality as CompositionNaturality
import SCT.VolumeI.Chapter01.Section04.Substitution.ParameterChangeNaturality as ParameterChangeNaturality
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ParameterSquarePasting as ParameterSquarePasting
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ParameterSquareNaturality as ParameterSquareNaturality
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ParameterSquareUnits as ParameterSquareUnits
import SCT.VolumeI.Chapter01.Section04.Substitution.ComparisonCancellation as ComparisonCancellation
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PairingUnits
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.UniversalCoherenceCalculus as UniversalCoherenceCalculus

module SCT.VolumeI.Chapter01.Section04.CompositionCalculus.UniversalCoherence
  {c m a : Level} (𝒯 : Theory c m a)
  (M : MappingAnimae.MappingAnimae 𝒯) where

open Setup 𝒯
open MappingAnimae.MappingAnimae M
open Currying 𝒯 M
open MapComposition 𝒯 M
open InternalCoherence 𝒯 M
open RetainedComparisonLaws 𝒯 M using
  (compose-triangle; module RetainedSquares; module RetainedNaturality; cancel-two-front)
open InternalPentagon 𝒯 M using (compose-pentagon; extend-square)
open ParameterChange 𝒯 M using
  (mapReflect-specialize-image; mapReflect-pre-image-β; mapUncurryIso-inverse; retained-parameter-change)
open ParameterChangeNaturality 𝒯 M using (retained-parameter-change-natural)
open ParameterSquarePasting 𝒯 using (paste)
open ParameterSquareNaturality 𝒯 using (paste-source-square; paste-source-normalization; paste-target-normalization;
    paste-natural-outer; paste-natural-inner; paste-comparison-chain;
    paste-comparison-chain-outer; paste-comparison-chain-inner)
open ParameterSquareUnits 𝒯 using (unit-square; paste-unitˡ; paste-unitʳ)
open CompositionNaturality 𝒯 M using (chain-input-squares)
open PairingCoherence vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-Iso₂; pair-iso-extensionality; pair-cong-comp)
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-left-reflect; cancel-left)
open PairingUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (cancel-right-reflect)
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-comp-at; preWhisker-comp-at; whisker-mixed-at; postWhisker-id-at; preWhisker-id-at)

open UniversalCoherenceCalculus 𝒯 M public

opaque
  paste-natural : {A₀ A₁ A₂ B₀ B₁ B₂ : CAT}
    {f f′ : MAP A₀ A₁} {g g′ : MAP A₁ A₂} {F F′ : MAP B₀ B₁} {G G′ : MAP B₁ B₂}
    {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂}
    (β : (x₂ ∘ g) =₁ (G ∘ x₁)) (β′ : (x₂ ∘ g′) =₁ (G′ ∘ x₁))
    (α : (x₁ ∘ f) =₁ (F ∘ x₀)) (α′ : (x₁ ∘ f′) =₁ (F′ ∘ x₀))
    (θ : g =₁ g′) (η : f =₁ f′) (ψ : G =₁ G′) (φ : F =₁ F′)
    → ((ψ ▷ x₁) ∙ β) =₂ (β′ ∙ (x₂ ◁ θ))
    → ((φ ▷ x₀) ∙ α) =₂ (α′ ∙ (x₁ ◁ η))
    → (((ψ ⋆ φ) ▷ x₀) ∙ paste β α) =₂ (paste β′ α′ ∙ (x₂ ◁ (θ ⋆ η)))
  paste-natural = ParameterSquareNaturality.paste-natural 𝒯

  unchanged-parameter-square : {A B C D : CAT}
    {f : MAP A B} {F : MAP C D} {x : MAP A C} {y : MAP B D}
    (α : (y ∘ f) =₁ (F ∘ x))
    → ((idIso F ▷ x) ∙ α) =₂ (α ∙ (y ◁ idIso f))
  unchanged-parameter-square = ParameterSquareNaturality.unchanged-parameter-square 𝒯

module AssociatorChange {P Q A B C D : CAT} (σ : MAP Q P)
  (h : MAP P (Map C D)) (g : MAP P (Map B C)) (f : MAP P (Map A B))
  {h′ : MAP Q (Map C D)} {g′ : MAP Q (Map B C)} {f′ : MAP Q (Map A B)}
  (Lh : (h ∘ σ) =₁ h′) (Lg : (g ∘ σ) =₁ g′) (Lf : (f ∘ σ) =₁ f′) where

  private
    module RP = RetainedEvaluation P
    module RQ = RetainedEvaluation Q
    module N (X Y : CAT) = NormalizedChange {C = X} {D = Y} σ
    module NC = NormalizedComposition σ
    module RoutesP = RouteNaturality P
    module RoutesQ = RouteNaturality Q
    module Pasting = ParameterSquarePasting.Coherence 𝒯 M

  s : (X : CAT) → MAP (Q × X) (P × X)
  s X = productMap σ (id X)

  Lhg : (composeTerm h g ∘ σ) =₁ (composeTerm h′ g′)
  Lhg = composeTerm-evaluate h g σ Lh Lg
  Lgf : (composeTerm g f ∘ σ) =₁ (composeTerm g′ f′)
  Lgf = composeTerm-evaluate g f σ Lg Lf
  Lleft : (composeTerm (composeTerm h g) f ∘ σ) =₁ (composeTerm (composeTerm h′ g′) f′)
  Lleft = composeTerm-evaluate (composeTerm h g) f σ Lhg Lf
  Lright : (composeTerm h (composeTerm g f) ∘ σ) =₁ (composeTerm h′ (composeTerm g′ f′))
  Lright = composeTerm-evaluate h (composeTerm g f) σ Lh Lgf

  κh : (s D ∘ RQ.retained h′) =₁ (RP.retained h ∘ s C)
  κh = N.change C D h Lh
  κg : (s C ∘ RQ.retained g′) =₁ (RP.retained g ∘ s B)
  κg = N.change B C g Lg
  κf : (s B ∘ RQ.retained f′) =₁ (RP.retained f ∘ s A)
  κf = N.change A B f Lf
  κhg : (s D ∘ RQ.retained (composeTerm h′ g′)) =₁ (RP.retained (composeTerm h g) ∘ s B)
  κhg = N.change B D (composeTerm h g) Lhg
  κgf : (s C ∘ RQ.retained (composeTerm g′ f′)) =₁ (RP.retained (composeTerm g f) ∘ s A)
  κgf = N.change A C (composeTerm g f) Lgf
  κleft : (s D ∘ RQ.retained (composeTerm (composeTerm h′ g′) f′)) =₁
    (RP.retained (composeTerm (composeTerm h g) f) ∘ s A)
  κleft = N.change A D (composeTerm (composeTerm h g) f) Lleft
  κright : (s D ∘ RQ.retained (composeTerm h′ (composeTerm g′ f′))) =₁
    (RP.retained (composeTerm h (composeTerm g f)) ∘ s A)
  κright = N.change A D (composeTerm h (composeTerm g f)) Lright

  leftP : (RP.retained (composeTerm (composeTerm h g) f)) =₁
    ((RP.retained h ∘ RP.retained g) ∘ RP.retained f)
  leftP = RoutesP.left-comparison h g f
  rightP : (RP.retained (composeTerm h (composeTerm g f))) =₁
    (RP.retained h ∘ (RP.retained g ∘ RP.retained f))
  rightP = RoutesP.right-comparison h g f
  leftQ : (RQ.retained (composeTerm (composeTerm h′ g′) f′)) =₁
    ((RQ.retained h′ ∘ RQ.retained g′) ∘ RQ.retained f′)
  leftQ = RoutesQ.left-comparison h′ g′ f′
  rightQ : (RQ.retained (composeTerm h′ (composeTerm g′ f′))) =₁
    (RQ.retained h′ ∘ (RQ.retained g′ ∘ RQ.retained f′))
  rightQ = RoutesQ.right-comparison h′ g′ f′

  opaque
    left-comparison-change : NC.BasicSquare h g → NC.BasicSquare (composeTerm h g) f
      → (paste (paste κh κg) κf ∙ (s D ◁ leftQ)) =₂ ((leftP ▷ s A) ∙ κleft)
    left-comparison-change hg outer =
      paste-comparison-chain-outer
        κleft κhg (paste κh κg) κf
        (RQ.retained-compose (composeTerm h′ g′) f′)
        (RP.retained-compose (composeTerm h g) f)
        (RQ.retained-compose h′ g′) (RP.retained-compose h g)
        (NC.normalize (composeTerm h g) f Lhg Lf outer)
        ((NC.normalize h g Lh Lg hg) ⁻¹)

    right-comparison-change : NC.BasicSquare g f → NC.BasicSquare h (composeTerm g f)
      → (paste κh (paste κg κf) ∙ (s D ◁ rightQ)) =₂ ((rightP ▷ s A) ∙ κright)
    right-comparison-change gf outer =
      paste-comparison-chain-inner
        κright κh κgf (paste κg κf)
        (RQ.retained-compose h′ (composeTerm g′ f′))
        (RP.retained-compose h (composeTerm g f))
        (RQ.retained-compose g′ f′) (RP.retained-compose g f)
        (NC.normalize h (composeTerm g f) Lh Lgf outer)
        ((NC.normalize g f Lg Lf gf) ⁻¹)

    route : NC.BasicSquare h g → NC.BasicSquare g f
      → NC.BasicSquare (composeTerm h g) f → NC.BasicSquare h (composeTerm g f)
      → (κright ∙ (s D ◁ RQ.associator-route h′ g′ f′)) =₂
          ((RP.associator-route h g f ▷ s A) ∙ κleft)
    route hg gf outerLeft outerRight =
      let KL : (s D ∘ ((RQ.retained h′ ∘ RQ.retained g′) ∘ RQ.retained f′)) =₁
            (((RP.retained h ∘ RP.retained g) ∘ RP.retained f) ∘ s A)
          KL = paste (paste κh κg) κf
          KR : (s D ∘ (RQ.retained h′ ∘ (RQ.retained g′ ∘ RQ.retained f′))) =₁
            ((RP.retained h ∘ (RP.retained g ∘ RP.retained f)) ∘ s A)
          KR = paste κh (paste κg κf)
          AP = comp-assoc (RP.retained f) (RP.retained g) (RP.retained h)
          AQ = comp-assoc (RQ.retained f′) (RQ.retained g′) (RQ.retained h′)
          routeP = RP.associator-route h g f
          routeQ = RQ.associator-route h′ g′ f′
          qSquare : ((s D ◁ rightQ) ∙ (s D ◁ routeQ)) =₂ ((s D ◁ AQ) ∙ (s D ◁ leftQ))
          qSquare = postWhisker-isoComp-at (s D) AQ leftQ ∙
            ((postWhisker (s D) ◁ RoutesQ.route-square h′ g′ f′) ∙
              (postWhisker-isoComp-at (s D) rightQ routeQ) ⁻¹)
          pSquare : ((rightP ▷ s A) ∙ (routeP ▷ s A)) =₂ ((AP ▷ s A) ∙ (leftP ▷ s A))
          pSquare = preWhisker-isoComp-at AP leftP (s A) ∙
            ((preWhisker (s A) ◁ RoutesP.route-square h g f) ∙
              (preWhisker-isoComp-at rightP routeP (s A)) ⁻¹)
      in ComparisonCancellation.transport-route-square 𝒯
        (s D ◁ leftQ) (s D ◁ rightQ) (s D ◁ AQ) (s D ◁ routeQ)
        (leftP ▷ s A) (rightP ▷ s A) (AP ▷ s A) (routeP ▷ s A)
        κleft κright KL KR qSquare pSquare
        (left-comparison-change hg outerLeft) (right-comparison-change gf outerRight)
        (Pasting.paste-assoc
          {f = RQ.retained f′} {g = RQ.retained g′} {h = RQ.retained h′}
          {F = RP.retained f} {G = RP.retained g} {H = RP.retained h}
          {x₀ = s A} {x₁ = s B} {x₂ = s C} {x₃ = s D} κh κg κf)
```

The following formulas compute the images of the actual normalized
universal comparisons. Their target parameter can be any category. They
use the image of a restricted lift and the explicit endpoint comparisons
appearing in `internalUnit` and `internalAssoc`.

```agda
specialized-image : {P Q C D : CAT} (pAn : isAn P)
  (f g : MAP P (Map C D)) (α : (mapUncurry f) =₁ (mapUncurry g)) (σ : MAP Q P)
  {f′ g′ : MAP Q (Map C D)} (left : (f ∘ σ) =₁ f′) (right : (g ∘ σ) =₁ g′)
  → (mapUncurryIso (specialize (mapReflect pAn f g α) σ left right)) =₂
      (mapReflect-specialize-image f g α σ left right)
specialized-image pAn f g α σ left right =
  let lifted = mapReflect pAn f g α
  in isoComp-cong (idIso (mapUncurryIso right))
      (isoComp-cong (mapReflect-pre-image-β pAn f g α σ) (mapUncurryIso-inverse left)) ∙
    (isoComp-cong (idIso (mapUncurryIso right)) (mapUncurryIso-comp (lifted ▷ σ) (left ⁻¹)) ∙
      mapUncurryIso-comp right ((lifted ▷ σ) ∙ left ⁻¹)) ∙
    mapUncurry-Iso₂ (isoComp-assoc-at right (lifted ▷ σ) (left ⁻¹))

module UnitRestriction {Q C D : CAT} (f : MAP Q (Map C D)) where
  universal = id (Map C D)

  left-boundary = composeTerm-evaluate (identityTerm D) universal f
    (const-pre (mapId D) f) (comp-unitˡ f)
  right-boundary = composeTerm-evaluate universal (identityTerm C) f
    (comp-unitˡ f) (const-pre (mapId C) f)

  left-image = mapReflect-specialize-image (composeTerm (identityTerm D) universal) universal
    (evaluate-retained-left-unit universal) f left-boundary (comp-unitˡ f)
  right-image = mapReflect-specialize-image (composeTerm universal (identityTerm C)) universal
    (evaluate-retained-right-unit universal) f right-boundary (comp-unitˡ f)

  left-image-β : (mapUncurryIso (internalUnitˡ f)) =₂ left-image
  left-image-β = specialized-image (map-isAn C D) _ _
    (evaluate-retained-left-unit universal) f left-boundary (comp-unitˡ f)

  right-image-β : (mapUncurryIso (internalUnitʳ f)) =₂ right-image
  right-image-β = specialized-image (map-isAn C D) _ _
    (evaluate-retained-right-unit universal) f right-boundary (comp-unitˡ f)

  private
    module N = NormalizedChange {C = C} {D = D} f
    module RP = RetainedEvaluation (Map C D)
    module RQ = RetainedEvaluation Q

  LeftRouteSquare : Set m
  LeftRouteSquare =
    (N.change universal (comp-unitˡ f) ∙ (N.t ◁ RQ.left-unit-route f)) =₂
    ((RP.left-unit-route universal ▷ N.s) ∙
      N.change (composeTerm (identityTerm D) universal) left-boundary)

  RightRouteSquare : Set m
  RightRouteSquare =
    (N.change universal (comp-unitˡ f) ∙ (N.t ◁ RQ.right-unit-route f)) =₂
    ((RP.right-unit-route universal ▷ N.s) ∙
      N.change (composeTerm universal (identityTerm C)) right-boundary)

  left-from-route-square : (qAn : isAn Q) → LeftRouteSquare
    → (internalUnitˡ f) =₂ (compose-unitˡ qAn f)
  left-from-route-square qAn = N.reflect-route (mapComp-unitˡ C D) left-boundary (comp-unitˡ f)
    qAn (RP.left-unit-route universal) (RQ.left-unit-route f)
    (RetainedSquares.compose-unitˡ-retained-β (Map C D) (map-isAn C D) universal)
    (RetainedSquares.left-unit-route-base Q f)

  right-from-route-square : (qAn : isAn Q) → RightRouteSquare
    → (internalUnitʳ f) =₂ (compose-unitʳ qAn f)
  right-from-route-square qAn = N.reflect-route (mapComp-unitʳ C D) right-boundary (comp-unitˡ f)
    qAn (RP.right-unit-route universal) (RQ.right-unit-route f)
    (RetainedSquares.compose-unitʳ-retained-β (Map C D) (map-isAn C D) universal)
    (RetainedSquares.right-unit-route-base Q f)

module AssocRestriction {Q A B C D : CAT}
  (h : MAP Q (Map C D)) (g : MAP Q (Map B C)) (f : MAP Q (Map A B)) where
  P = (Map C D × Map B C) × Map A B
  pAn = product-isAn (product-isAn (map-isAn C D) (map-isAn B C)) (map-isAn A B)

  universal-h : MAP P (Map C D)
  universal-h = pr₁ ∘ pr₁
  universal-g : MAP P (Map B C)
  universal-g = pr₂ ∘ pr₁
  universal-f : MAP P (Map A B)
  universal-f = pr₂

  point = pair (pair h g) f
  first = pair-β₁ h g ∙
    ((pr₁ ◁ pair-β₁ (pair h g) f) ∙ comp-assoc point pr₁ pr₁)
  second = pair-β₂ h g ∙
    ((pr₂ ◁ pair-β₁ (pair h g) f) ∙ comp-assoc point pr₁ pr₂)
  third = pair-β₂ (pair h g) f

  left-boundary = composeTerm-evaluate (composeTerm universal-h universal-g) universal-f point
    (composeTerm-evaluate universal-h universal-g point first second) third
  right-boundary = composeTerm-evaluate universal-h (composeTerm universal-g universal-f) point first
    (composeTerm-evaluate universal-g universal-f point second third)

  image = mapReflect-specialize-image (composeTerm (composeTerm universal-h universal-g) universal-f)
    (composeTerm universal-h (composeTerm universal-g universal-f))
    (evaluate-assoc universal-h universal-g universal-f) point left-boundary right-boundary

  image-β : (mapUncurryIso (internalAssoc h g f)) =₂ image
  image-β = specialized-image pAn _ _
    (evaluate-assoc universal-h universal-g universal-f) point left-boundary right-boundary

  private
    module N = NormalizedChange {C = A} {D = D} point
    module RP = RetainedEvaluation P
    module RQ = RetainedEvaluation Q

  RouteSquare : Set m
  RouteSquare =
    (N.change (composeTerm universal-h (composeTerm universal-g universal-f)) right-boundary ∙
      (N.t ◁ RQ.associator-route h g f)) =₂
    ((RP.associator-route universal-h universal-g universal-f ▷ N.s) ∙
      N.change (composeTerm (composeTerm universal-h universal-g) universal-f) left-boundary)

  from-route-square : (qAn : isAn Q) → RouteSquare
    → (internalAssoc h g f) =₂ (compose-assoc qAn h g f)
  from-route-square qAn = N.reflect-route
    {f = composeTerm (composeTerm universal-h universal-g) universal-f}
    {g = composeTerm universal-h (composeTerm universal-g universal-f)}
    (mapComp-assoc A B C D)
    {f′ = composeTerm (composeTerm h g) f}
    {g′ = composeTerm h (composeTerm g f)}
    left-boundary right-boundary
    qAn (RP.associator-route universal-h universal-g universal-f) (RQ.associator-route h g f)
    (RetainedSquares.compose-assoc-retained-β P {A = A} {B = B} {C = C} {D = D}
      pAn universal-h universal-g universal-f)
    (RetainedSquares.associator-route-base Q {A = A} {B = B} {C = C} {D = D} h g f)

universal-left-unit-from-image : {P C D : CAT} (pAn : isAn P) (f : MAP P (Map C D))
  → (mapUncurryIso (internalUnitˡ f)) =₂ (evaluate-retained-left-unit f)
  → (internalUnitˡ f) =₂ (compose-unitˡ pAn f)
universal-left-unit-from-image pAn f image = mapReflect-Iso₂ pAn _ _
  ((compose-unitˡ-β pAn f) ⁻¹ ∙ image)

universal-right-unit-from-image : {P C D : CAT} (pAn : isAn P) (f : MAP P (Map C D))
  → (mapUncurryIso (internalUnitʳ f)) =₂ (evaluate-retained-right-unit f)
  → (internalUnitʳ f) =₂ (compose-unitʳ pAn f)
universal-right-unit-from-image pAn f image = mapReflect-Iso₂ pAn _ _
  ((compose-unitʳ-β pAn f) ⁻¹ ∙ image)

universal-assoc-from-image : {P A B C D : CAT} (pAn : isAn P)
  (h : MAP P (Map C D)) (g : MAP P (Map B C)) (f : MAP P (Map A B))
  → (mapUncurryIso (internalAssoc h g f)) =₂ (evaluate-assoc h g f)
  → (internalAssoc h g f) =₂ (compose-assoc pAn h g f)
universal-assoc-from-image pAn h g f image = mapReflect-Iso₂ pAn _ _
  ((compose-assoc-β pAn h g f) ⁻¹ ∙ image)

universal-left-unit-from-restriction : {P C D : CAT} (pAn : isAn P) (f : MAP P (Map C D))
  → (UnitRestriction.left-image f) =₂ (evaluate-retained-left-unit f)
  → (internalUnitˡ f) =₂ (compose-unitˡ pAn f)
universal-left-unit-from-restriction pAn f p =
  universal-left-unit-from-image pAn f (p ∙ UnitRestriction.left-image-β f)

universal-right-unit-from-restriction : {P C D : CAT} (pAn : isAn P) (f : MAP P (Map C D))
  → (UnitRestriction.right-image f) =₂ (evaluate-retained-right-unit f)
  → (internalUnitʳ f) =₂ (compose-unitʳ pAn f)
universal-right-unit-from-restriction pAn f p =
  universal-right-unit-from-image pAn f (p ∙ UnitRestriction.right-image-β f)

universal-assoc-from-restriction : {P A B C D : CAT} (pAn : isAn P)
  (h : MAP P (Map C D)) (g : MAP P (Map B C)) (f : MAP P (Map A B))
  → (AssocRestriction.image h g f) =₂ (evaluate-assoc h g f)
  → (internalAssoc h g f) =₂ (compose-assoc pAn h g f)
universal-assoc-from-restriction pAn h g f p =
  universal-assoc-from-image pAn h g f (p ∙ AssocRestriction.image-β h g f)

module RetainedTests {P Q : CAT} (pAn : isAn P) (σ : MAP P Q) where
  open RetainedEvaluation P
  open RetainedSquares P
  open ParameterReflection σ

  left-unit : {C D : CAT} (f : MAP P (Map C D))
    → (productMap σ (id D) ◁ retainedIso (internalUnitˡ f)) =₂
        (productMap σ (id D) ◁ left-unit-route f)
    → (internalUnitˡ f) =₂ (compose-unitˡ pAn f)
  left-unit f p = retainedIso-reflect pAn _ _
    ((compose-unitˡ-retained-β pAn f) ⁻¹ ∙
      retained-comparison (retainedIso-base (internalUnitˡ f)) (left-unit-route-base f) p)

  right-unit : {C D : CAT} (f : MAP P (Map C D))
    → (productMap σ (id D) ◁ retainedIso (internalUnitʳ f)) =₂
        (productMap σ (id D) ◁ right-unit-route f)
    → (internalUnitʳ f) =₂ (compose-unitʳ pAn f)
  right-unit f p = retainedIso-reflect pAn _ _
    ((compose-unitʳ-retained-β pAn f) ⁻¹ ∙
      retained-comparison (retainedIso-base (internalUnitʳ f)) (right-unit-route-base f) p)

  associator : {A B C D : CAT}
    (h : MAP P (Map C D)) (g : MAP P (Map B C)) (f : MAP P (Map A B))
    → (productMap σ (id D) ◁ retainedIso (internalAssoc h g f)) =₂
        (productMap σ (id D) ◁ associator-route h g f)
    → (internalAssoc h g f) =₂ (compose-assoc pAn h g f)
  associator h g f p = retainedIso-reflect pAn _ _
    ((compose-assoc-retained-β pAn h g f) ⁻¹ ∙
      retained-comparison (retainedIso-base (internalAssoc h g f)) (associator-route-base h g f) p)
```

The transferred statements below have precisely the boundaries of
`Triangle.Statement` and `Pentagon.Statement` in `InternalCoherence`.
Their comparison inputs are proof obligations, not replacements for those
boundaries by different choices. The triangle and pentagon transfer laws
assemble their three and five specified edge comparisons. Their transparent
pastings and higher computation statements record the resulting witnesses.

```agda
universal-triangle-from-comparisons : {P A B C : CAT} (pAn : isAn P)
  (g : MAP P (Map B C)) (f : MAP P (Map A B))
  → (internalUnitʳ g) =₂ (compose-unitʳ pAn g)
  → (internalUnitˡ f) =₂ (compose-unitˡ pAn f)
  → (internalAssoc g (identityTerm B) f) =₂ (compose-assoc pAn g (identityTerm B) f)
  → Triangle.Statement g f
universal-triangle-from-comparisons {B = B} pAn g f right-unit left-unit assoc =
  ComparisonCancellation.TriangleTransport.transport 𝒯
    (composeTerm-cong (internalUnitʳ g) (idIso f))
    (composeTerm-cong (compose-unitʳ pAn g) (idIso f))
    (internalAssoc g (identityTerm B) f) (compose-assoc pAn g (identityTerm B) f)
    (composeTerm-cong (idIso g) (internalUnitˡ f))
    (composeTerm-cong (idIso g) (compose-unitˡ pAn f))
    (composeTerm-Iso₂ right-unit (idIso (idIso f))) assoc
    (composeTerm-Iso₂ (idIso (idIso g)) left-unit)
    (compose-triangle pAn g f)

universal-pentagon-from-comparisons : {P A B C D E : CAT} (pAn : isAn P)
  (k : MAP P (Map D E)) (h : MAP P (Map C D))
  (g : MAP P (Map B C)) (f : MAP P (Map A B))
  → (internalAssoc (composeTerm k h) g f) =₂ (compose-assoc pAn (composeTerm k h) g f)
  → (internalAssoc k h (composeTerm g f)) =₂ (compose-assoc pAn k h (composeTerm g f))
  → (internalAssoc k h g) =₂ (compose-assoc pAn k h g)
  → (internalAssoc k (composeTerm h g) f) =₂ (compose-assoc pAn k (composeTerm h g) f)
  → (internalAssoc h g f) =₂ (compose-assoc pAn h g f)
  → Pentagon.Statement k h g f
universal-pentagon-from-comparisons pAn k h g f a b c d e =
  ComparisonCancellation.PentagonTransport.transport 𝒯
    (internalAssoc (composeTerm k h) g f) (compose-assoc pAn (composeTerm k h) g f)
    (internalAssoc k h (composeTerm g f)) (compose-assoc pAn k h (composeTerm g f))
    (composeTerm-cong (internalAssoc k h g) (idIso f))
    (composeTerm-cong (compose-assoc pAn k h g) (idIso f))
    (internalAssoc k (composeTerm h g) f) (compose-assoc pAn k (composeTerm h g) f)
    (composeTerm-cong (idIso k) (internalAssoc h g f))
    (composeTerm-cong (idIso k) (compose-assoc pAn h g f))
    a b (composeTerm-Iso₂ c (idIso (idIso f))) d
    (composeTerm-Iso₂ (idIso (idIso k)) e)
    (compose-pentagon pAn k h g f)
```
