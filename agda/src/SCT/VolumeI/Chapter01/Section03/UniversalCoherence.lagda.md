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
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as MappingAnimae
import SCT.VolumeI.Chapter01.Section03.Currying as Currying
import SCT.VolumeI.Chapter01.Section03.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section03.InternalCoherence as InternalCoherence
import SCT.VolumeI.Chapter01.Section03.CompositionPentagon as CompositionPentagon
import SCT.VolumeI.Chapter01.Section03.InternalPentagon as InternalPentagon
import SCT.VolumeI.Chapter01.Section03.ParameterChange as ParameterChange
import SCT.VolumeI.Chapter01.Section03.CompositionNaturality as CompositionNaturality
import SCT.VolumeI.Chapter01.Section03.ParameterChangeNaturality as ParameterChangeNaturality
import SCT.VolumeI.Chapter01.Section03.ParameterSquarePasting as ParameterSquarePasting
import SCT.VolumeI.Chapter01.Section03.ParameterSquareNaturality as ParameterSquareNaturality
import SCT.VolumeI.Chapter01.Section03.ParameterSquareUnits as ParameterSquareUnits
import SCT.VolumeI.Chapter01.Section03.ComparisonCancellation as ComparisonCancellation
import SCT.VolumeI.Chapter01.Section02.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section02.PairingUnits as PairingUnits
import SCT.VolumeI.Chapter01.Section02.Structural as Structural
import SCT.VolumeI.Chapter01.Section02.IteratedPairing as IteratedPairing

import SCT.VolumeI.Chapter01.Section03.UniversalCoherenceCalculus as UniversalCoherenceCalculus

module SCT.VolumeI.Chapter01.Section03.UniversalCoherence
  {c m a : Level} (𝒯 : Theory c m a)
  (M : MappingAnimae.MappingAnimae 𝒯) where

open Setup 𝒯
open MappingAnimae.MappingAnimae M
open Currying 𝒯 M
open MapComposition 𝒯 M
open InternalCoherence 𝒯 M
open CompositionPentagon 𝒯 M using
  (compose-triangle; module RetainedSquares; module RetainedNaturality; cancel-two-front)
open InternalPentagon 𝒯 M using (compose-pentagon; extend-square)
open ParameterChange 𝒯 M using
  (mapReflect-specialize-image; mapReflect-pre-image-β; mapUncurryIso-inverse; retained-parameter-change)
open ParameterChangeNaturality 𝒯 M using (retained-parameter-change-natural)
open ParameterSquarePasting 𝒯 using (paste)
open ParameterSquareNaturality 𝒯 using (paste-source-square; paste-source-normalization; paste-target-normalization)
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
open IteratedPairing vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (hcomp-idOuter; hcomp-idInner)

open UniversalCoherenceCalculus 𝒯 M public

opaque
  paste-natural : {A₀ A₁ A₂ B₀ B₁ B₂ : CAT}
    {f f′ : MAP A₀ A₁} {g g′ : MAP A₁ A₂} {F F′ : MAP B₀ B₁} {G G′ : MAP B₁ B₂}
    {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂}
    (β : NatIso (x₂ ∘ g) (G ∘ x₁)) (β′ : NatIso (x₂ ∘ g′) (G′ ∘ x₁))
    (α : NatIso (x₁ ∘ f) (F ∘ x₀)) (α′ : NatIso (x₁ ∘ f′) (F′ ∘ x₀))
    (θ : NatIso g g′) (η : NatIso f f′) (ψ : NatIso G G′) (φ : NatIso F F′)
    → Iso₂ ((ψ ▷ x₁) ∙ β) (β′ ∙ (x₂ ◁ θ))
    → Iso₂ ((φ ▷ x₀) ∙ α) (α′ ∙ (x₁ ◁ η))
    → Iso₂ (((ψ ⋆ φ) ▷ x₀) ∙ paste β α) (paste β′ α′ ∙ (x₂ ◁ (θ ⋆ η)))
  paste-natural {x₀ = x₀} {x₁} β β′ α α′ θ η ψ φ b a = invIso
    (paste-target-normalization β α ψ φ ∙
      paste-source-square ((ψ ▷ x₁) ∙ β) β′ ((φ ▷ x₀) ∙ α) α′ θ η (invIso b) (invIso a))

  unchanged-parameter-square : {A B C D : CAT}
    {f : MAP A B} {F : MAP C D} {x : MAP A C} {y : MAP B D}
    (α : NatIso (y ∘ f) (F ∘ x))
    → Iso₂ ((idIso F ▷ x) ∙ α) (α ∙ (y ◁ idIso f))
  unchanged-parameter-square {f = f} {F} {x} {y} α =
    isoComp-cong (idIso α) (invIso (postWhisker-idIso y f)) ∙
    (invIso (isoComp-unitʳ-at α) ∙
    (isoComp-unitˡ-at α ∙ isoComp-cong (preWhisker-idIso F x) (idIso α)))

module AssociatorChange {P Q A B C D : CAT} (σ : MAP Q P)
  (h : MAP P (Map C D)) (g : MAP P (Map B C)) (f : MAP P (Map A B))
  {h′ : MAP Q (Map C D)} {g′ : MAP Q (Map B C)} {f′ : MAP Q (Map A B)}
  (Lh : NatIso (h ∘ σ) h′) (Lg : NatIso (g ∘ σ) g′) (Lf : NatIso (f ∘ σ) f′) where

  module RP = RetainedEvaluation P
  module RQ = RetainedEvaluation Q
  module N (X Y : CAT) = NormalizedChange {C = X} {D = Y} σ
  module NC = NormalizedComposition σ
  module RoutesP = RouteNaturality P
  module RoutesQ = RouteNaturality Q
  module Pasting = ParameterSquarePasting.Coherence 𝒯 M

  s : (X : CAT) → MAP (Q × X) (P × X)
  s X = productMap σ (id X)

  Lhg : NatIso (composeTerm h g ∘ σ) (composeTerm h′ g′)
  Lhg = composeTerm-evaluate h g σ Lh Lg
  Lgf : NatIso (composeTerm g f ∘ σ) (composeTerm g′ f′)
  Lgf = composeTerm-evaluate g f σ Lg Lf
  Lleft : NatIso (composeTerm (composeTerm h g) f ∘ σ) (composeTerm (composeTerm h′ g′) f′)
  Lleft = composeTerm-evaluate (composeTerm h g) f σ Lhg Lf
  Lright : NatIso (composeTerm h (composeTerm g f) ∘ σ) (composeTerm h′ (composeTerm g′ f′))
  Lright = composeTerm-evaluate h (composeTerm g f) σ Lh Lgf

  κh : NatIso (s D ∘ RQ.retained h′) (RP.retained h ∘ s C)
  κh = N.change C D h Lh
  κg : NatIso (s C ∘ RQ.retained g′) (RP.retained g ∘ s B)
  κg = N.change B C g Lg
  κf : NatIso (s B ∘ RQ.retained f′) (RP.retained f ∘ s A)
  κf = N.change A B f Lf
  κhg : NatIso (s D ∘ RQ.retained (composeTerm h′ g′)) (RP.retained (composeTerm h g) ∘ s B)
  κhg = N.change B D (composeTerm h g) Lhg
  κgf : NatIso (s C ∘ RQ.retained (composeTerm g′ f′)) (RP.retained (composeTerm g f) ∘ s A)
  κgf = N.change A C (composeTerm g f) Lgf
  κleft : NatIso (s D ∘ RQ.retained (composeTerm (composeTerm h′ g′) f′))
    (RP.retained (composeTerm (composeTerm h g) f) ∘ s A)
  κleft = N.change A D (composeTerm (composeTerm h g) f) Lleft
  κright : NatIso (s D ∘ RQ.retained (composeTerm h′ (composeTerm g′ f′)))
    (RP.retained (composeTerm h (composeTerm g f)) ∘ s A)
  κright = N.change A D (composeTerm h (composeTerm g f)) Lright

  leftP : NatIso (RP.retained (composeTerm (composeTerm h g) f))
    ((RP.retained h ∘ RP.retained g) ∘ RP.retained f)
  leftP = RoutesP.left-comparison h g f
  rightP : NatIso (RP.retained (composeTerm h (composeTerm g f)))
    (RP.retained h ∘ (RP.retained g ∘ RP.retained f))
  rightP = RoutesP.right-comparison h g f
  leftQ : NatIso (RQ.retained (composeTerm (composeTerm h′ g′) f′))
    ((RQ.retained h′ ∘ RQ.retained g′) ∘ RQ.retained f′)
  leftQ = RoutesQ.left-comparison h′ g′ f′
  rightQ : NatIso (RQ.retained (composeTerm h′ (composeTerm g′ f′)))
    (RQ.retained h′ ∘ (RQ.retained g′ ∘ RQ.retained f′))
  rightQ = RoutesQ.right-comparison h′ g′ f′

  opaque
    left-comparison-change : NC.BasicSquare h g → NC.BasicSquare (composeTerm h g) f
      → Iso₂ (paste (paste κh κg) κf ∙ (s D ◁ leftQ)) ((leftP ▷ s A) ∙ κleft)
    left-comparison-change hg outer =
      let inner = NC.normalize h g Lh Lg hg
          outerSquare = NC.normalize (composeTerm h g) f Lhg Lf outer
          cp = RP.retained-compose h g
          cq = RQ.retained-compose h′ g′
          op = RP.retained-compose (composeTerm h g) f
          oq = RQ.retained-compose (composeTerm h′ g′) f′
          p : NatIso (s D ∘ (RQ.retained (composeTerm h′ g′) ∘ RQ.retained f′))
            ((RP.retained (composeTerm h g) ∘ RP.retained f) ∘ s A)
          p = paste κhg κf
          p′ : NatIso (s D ∘ ((RQ.retained h′ ∘ RQ.retained g′) ∘ RQ.retained f′))
            (((RP.retained h ∘ RP.retained g) ∘ RP.retained f) ∘ s A)
          p′ = paste (paste κh κg) κf
          natural : Iso₂ (((cp ▷ RP.retained f) ▷ s A) ∙ p)
            (p′ ∙ (s D ◁ (cq ▷ RQ.retained f′)))
          natural = isoComp-cong (idIso p′) (postWhisker (s D) ◁ hcomp-idInner cq (RQ.retained f′)) ∙
            (paste-natural
              {f = RQ.retained f′} {f′ = RQ.retained f′}
              {g = RQ.retained (composeTerm h′ g′)} {g′ = RQ.retained h′ ∘ RQ.retained g′}
              {F = RP.retained f} {F′ = RP.retained f}
              {G = RP.retained (composeTerm h g)} {G′ = RP.retained h ∘ RP.retained g}
              {x₀ = s A} {x₁ = s B} {x₂ = s D}
              κhg (paste κh κg) κf κf cq (idIso (RQ.retained f′))
              cp (idIso (RP.retained f)) (invIso inner) (unchanged-parameter-square κf) ∙
              isoComp-cong (preWhisker (s A) ◁ invIso (hcomp-idInner cp (RP.retained f))) (idIso p))
      in isoComp-cong (invIso (preWhisker-isoComp-at (cp ▷ RP.retained f) op (s A))) (idIso κleft) ∙
        (invIso (paste-squares (s D ◁ oq) (op ▷ s A)
          (s D ◁ (cq ▷ RQ.retained f′)) ((cp ▷ RP.retained f) ▷ s A)
          κleft p p′ (invIso outerSquare) natural) ∙
          isoComp-cong (idIso p′) (postWhisker-isoComp-at (s D) (cq ▷ RQ.retained f′) oq))
    right-comparison-change : NC.BasicSquare g f → NC.BasicSquare h (composeTerm g f)
      → Iso₂ (paste κh (paste κg κf) ∙ (s D ◁ rightQ)) ((rightP ▷ s A) ∙ κright)
    right-comparison-change gf outer =
      let inner = NC.normalize g f Lg Lf gf
          outerSquare = NC.normalize h (composeTerm g f) Lh Lgf outer
          cp = RP.retained-compose g f
          cq = RQ.retained-compose g′ f′
          op = RP.retained-compose h (composeTerm g f)
          oq = RQ.retained-compose h′ (composeTerm g′ f′)
          p : NatIso (s D ∘ (RQ.retained h′ ∘ RQ.retained (composeTerm g′ f′)))
            ((RP.retained h ∘ RP.retained (composeTerm g f)) ∘ s A)
          p = paste κh κgf
          p′ : NatIso (s D ∘ (RQ.retained h′ ∘ (RQ.retained g′ ∘ RQ.retained f′)))
            ((RP.retained h ∘ (RP.retained g ∘ RP.retained f)) ∘ s A)
          p′ = paste κh (paste κg κf)
          natural : Iso₂ (((RP.retained h ◁ cp) ▷ s A) ∙ p)
            (p′ ∙ (s D ◁ (RQ.retained h′ ◁ cq)))
          natural = isoComp-cong (idIso p′) (postWhisker (s D) ◁ hcomp-idOuter (RQ.retained h′) cq) ∙
            (paste-natural
              {f = RQ.retained (composeTerm g′ f′)} {f′ = RQ.retained g′ ∘ RQ.retained f′}
              {g = RQ.retained h′} {g′ = RQ.retained h′}
              {F = RP.retained (composeTerm g f)} {F′ = RP.retained g ∘ RP.retained f}
              {G = RP.retained h} {G′ = RP.retained h}
              {x₀ = s A} {x₁ = s C} {x₂ = s D}
              κh κh κgf (paste κg κf) (idIso (RQ.retained h′)) cq
              (idIso (RP.retained h)) cp (unchanged-parameter-square κh) (invIso inner) ∙
              isoComp-cong (preWhisker (s A) ◁ invIso (hcomp-idOuter (RP.retained h) cp)) (idIso p))
      in isoComp-cong (invIso (preWhisker-isoComp-at (RP.retained h ◁ cp) op (s A))) (idIso κright) ∙
        (invIso (paste-squares (s D ◁ oq) (op ▷ s A)
          (s D ◁ (RQ.retained h′ ◁ cq)) ((RP.retained h ◁ cp) ▷ s A)
          κright p p′ (invIso outerSquare) natural) ∙
          isoComp-cong (idIso p′) (postWhisker-isoComp-at (s D) (RQ.retained h′ ◁ cq) oq))
    route : NC.BasicSquare h g → NC.BasicSquare g f
      → NC.BasicSquare (composeTerm h g) f → NC.BasicSquare h (composeTerm g f)
      → Iso₂ (κright ∙ (s D ◁ RQ.associator-route h′ g′ f′))
          ((RP.associator-route h g f ▷ s A) ∙ κleft)
    route hg gf outerLeft outerRight =
      let KL : NatIso (s D ∘ ((RQ.retained h′ ∘ RQ.retained g′) ∘ RQ.retained f′))
            (((RP.retained h ∘ RP.retained g) ∘ RP.retained f) ∘ s A)
          KL = paste (paste κh κg) κf
          KR : NatIso (s D ∘ (RQ.retained h′ ∘ (RQ.retained g′ ∘ RQ.retained f′)))
            ((RP.retained h ∘ (RP.retained g ∘ RP.retained f)) ∘ s A)
          KR = paste κh (paste κg κf)
          AP = comp-assoc (RP.retained f) (RP.retained g) (RP.retained h)
          AQ = comp-assoc (RQ.retained f′) (RQ.retained g′) (RQ.retained h′)
          routeP = RP.associator-route h g f
          routeQ = RQ.associator-route h′ g′ f′
          qSquare : Iso₂ ((s D ◁ rightQ) ∙ (s D ◁ routeQ)) ((s D ◁ AQ) ∙ (s D ◁ leftQ))
          qSquare = postWhisker-isoComp-at (s D) AQ leftQ ∙
            ((postWhisker (s D) ◁ RoutesQ.route-square h′ g′ f′) ∙
              invIso (postWhisker-isoComp-at (s D) rightQ routeQ))
          pSquare : Iso₂ ((rightP ▷ s A) ∙ (routeP ▷ s A)) ((AP ▷ s A) ∙ (leftP ▷ s A))
          pSquare = preWhisker-isoComp-at AP leftP (s A) ∙
            ((preWhisker (s A) ◁ RoutesP.route-square h g f) ∙
              invIso (preWhisker-isoComp-at rightP routeP (s A)))
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
  (f g : MAP P (Map C D)) (α : NatIso (mapUncurry f) (mapUncurry g)) (σ : MAP Q P)
  {f′ g′ : MAP Q (Map C D)} (left : NatIso (f ∘ σ) f′) (right : NatIso (g ∘ σ) g′)
  → Iso₂ (mapUncurryIso (specialize (mapReflect pAn f g α) σ left right))
      (mapReflect-specialize-image f g α σ left right)
specialized-image pAn f g α σ left right =
  let lifted = mapReflect pAn f g α
  in isoComp-cong (idIso (mapUncurryIso right))
      (isoComp-cong (mapReflect-pre-image-β pAn f g α σ) (mapUncurryIso-inverse left)) ∙
    (isoComp-cong (idIso (mapUncurryIso right)) (mapUncurryIso-comp (lifted ▷ σ) (invIso left)) ∙
      mapUncurryIso-comp right ((lifted ▷ σ) ∙ invIso left)) ∙
    mapUncurry-Iso₂ (isoComp-assoc-at right (lifted ▷ σ) (invIso left))

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

  left-image-β : Iso₂ (mapUncurryIso (internalUnitˡ f)) left-image
  left-image-β = specialized-image (map-isAn C D) _ _
    (evaluate-retained-left-unit universal) f left-boundary (comp-unitˡ f)

  right-image-β : Iso₂ (mapUncurryIso (internalUnitʳ f)) right-image
  right-image-β = specialized-image (map-isAn C D) _ _
    (evaluate-retained-right-unit universal) f right-boundary (comp-unitˡ f)

  module N = NormalizedChange {C = C} {D = D} f
  module RP = RetainedEvaluation (Map C D)
  module RQ = RetainedEvaluation Q

  LeftRouteSquare : Set m
  LeftRouteSquare = Iso₂
    (N.change universal (comp-unitˡ f) ∙ (N.t ◁ RQ.left-unit-route f))
    ((RP.left-unit-route universal ▷ N.s) ∙
      N.change (composeTerm (identityTerm D) universal) left-boundary)

  RightRouteSquare : Set m
  RightRouteSquare = Iso₂
    (N.change universal (comp-unitˡ f) ∙ (N.t ◁ RQ.right-unit-route f))
    ((RP.right-unit-route universal ▷ N.s) ∙
      N.change (composeTerm universal (identityTerm C)) right-boundary)

  left-from-route-square : (qAn : isAn Q) → LeftRouteSquare
    → Iso₂ (internalUnitˡ f) (compose-unitˡ qAn f)
  left-from-route-square qAn = N.reflect-route (mapComp-unitˡ C D) left-boundary (comp-unitˡ f)
    qAn (RP.left-unit-route universal) (RQ.left-unit-route f)
    (RetainedSquares.compose-unitˡ-retained-β (Map C D) (map-isAn C D) universal)
    (RetainedSquares.left-unit-route-base Q f)

  right-from-route-square : (qAn : isAn Q) → RightRouteSquare
    → Iso₂ (internalUnitʳ f) (compose-unitʳ qAn f)
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

  image-β : Iso₂ (mapUncurryIso (internalAssoc h g f)) image
  image-β = specialized-image pAn _ _
    (evaluate-assoc universal-h universal-g universal-f) point left-boundary right-boundary

  module N = NormalizedChange {C = A} {D = D} point
  module RP = RetainedEvaluation P
  module RQ = RetainedEvaluation Q

  RouteSquare : Set m
  RouteSquare = Iso₂
    (N.change (composeTerm universal-h (composeTerm universal-g universal-f)) right-boundary ∙
      (N.t ◁ RQ.associator-route h g f))
    ((RP.associator-route universal-h universal-g universal-f ▷ N.s) ∙
      N.change (composeTerm (composeTerm universal-h universal-g) universal-f) left-boundary)

  from-route-square : (qAn : isAn Q) → RouteSquare
    → Iso₂ (internalAssoc h g f) (compose-assoc qAn h g f)
  from-route-square qAn = N.reflect-route (mapComp-assoc A B C D) left-boundary right-boundary
    qAn (RP.associator-route universal-h universal-g universal-f) (RQ.associator-route h g f)
    (RetainedSquares.compose-assoc-retained-β P pAn universal-h universal-g universal-f)
    (RetainedSquares.associator-route-base Q h g f)

universal-left-unit-from-image : {P C D : CAT} (pAn : isAn P) (f : MAP P (Map C D))
  → Iso₂ (mapUncurryIso (internalUnitˡ f)) (evaluate-retained-left-unit f)
  → Iso₂ (internalUnitˡ f) (compose-unitˡ pAn f)
universal-left-unit-from-image pAn f image = mapReflect-Iso₂ pAn _ _
  (invIso (compose-unitˡ-β pAn f) ∙ image)

universal-right-unit-from-image : {P C D : CAT} (pAn : isAn P) (f : MAP P (Map C D))
  → Iso₂ (mapUncurryIso (internalUnitʳ f)) (evaluate-retained-right-unit f)
  → Iso₂ (internalUnitʳ f) (compose-unitʳ pAn f)
universal-right-unit-from-image pAn f image = mapReflect-Iso₂ pAn _ _
  (invIso (compose-unitʳ-β pAn f) ∙ image)

universal-assoc-from-image : {P A B C D : CAT} (pAn : isAn P)
  (h : MAP P (Map C D)) (g : MAP P (Map B C)) (f : MAP P (Map A B))
  → Iso₂ (mapUncurryIso (internalAssoc h g f)) (evaluate-assoc h g f)
  → Iso₂ (internalAssoc h g f) (compose-assoc pAn h g f)
universal-assoc-from-image pAn h g f image = mapReflect-Iso₂ pAn _ _
  (invIso (compose-assoc-β pAn h g f) ∙ image)

universal-left-unit-from-restriction : {P C D : CAT} (pAn : isAn P) (f : MAP P (Map C D))
  → Iso₂ (UnitRestriction.left-image f) (evaluate-retained-left-unit f)
  → Iso₂ (internalUnitˡ f) (compose-unitˡ pAn f)
universal-left-unit-from-restriction pAn f p =
  universal-left-unit-from-image pAn f (p ∙ UnitRestriction.left-image-β f)

universal-right-unit-from-restriction : {P C D : CAT} (pAn : isAn P) (f : MAP P (Map C D))
  → Iso₂ (UnitRestriction.right-image f) (evaluate-retained-right-unit f)
  → Iso₂ (internalUnitʳ f) (compose-unitʳ pAn f)
universal-right-unit-from-restriction pAn f p =
  universal-right-unit-from-image pAn f (p ∙ UnitRestriction.right-image-β f)

universal-assoc-from-restriction : {P A B C D : CAT} (pAn : isAn P)
  (h : MAP P (Map C D)) (g : MAP P (Map B C)) (f : MAP P (Map A B))
  → Iso₂ (AssocRestriction.image h g f) (evaluate-assoc h g f)
  → Iso₂ (internalAssoc h g f) (compose-assoc pAn h g f)
universal-assoc-from-restriction pAn h g f p =
  universal-assoc-from-image pAn h g f (p ∙ AssocRestriction.image-β h g f)

module RetainedTests {P Q : CAT} (pAn : isAn P) (σ : MAP P Q) where
  open RetainedEvaluation P
  open RetainedSquares P
  open ParameterReflection σ

  left-unit : {C D : CAT} (f : MAP P (Map C D))
    → Iso₂ (productMap σ (id D) ◁ retainedIso (internalUnitˡ f))
        (productMap σ (id D) ◁ left-unit-route f)
    → Iso₂ (internalUnitˡ f) (compose-unitˡ pAn f)
  left-unit f p = retainedIso-reflect pAn _ _
    (invIso (compose-unitˡ-retained-β pAn f) ∙
      retained-comparison (retainedIso-base (internalUnitˡ f)) (left-unit-route-base f) p)

  right-unit : {C D : CAT} (f : MAP P (Map C D))
    → Iso₂ (productMap σ (id D) ◁ retainedIso (internalUnitʳ f))
        (productMap σ (id D) ◁ right-unit-route f)
    → Iso₂ (internalUnitʳ f) (compose-unitʳ pAn f)
  right-unit f p = retainedIso-reflect pAn _ _
    (invIso (compose-unitʳ-retained-β pAn f) ∙
      retained-comparison (retainedIso-base (internalUnitʳ f)) (right-unit-route-base f) p)

  associator : {A B C D : CAT}
    (h : MAP P (Map C D)) (g : MAP P (Map B C)) (f : MAP P (Map A B))
    → Iso₂ (productMap σ (id D) ◁ retainedIso (internalAssoc h g f))
        (productMap σ (id D) ◁ associator-route h g f)
    → Iso₂ (internalAssoc h g f) (compose-assoc pAn h g f)
  associator h g f p = retainedIso-reflect pAn _ _
    (invIso (compose-assoc-retained-β pAn h g f) ∙
      retained-comparison (retainedIso-base (internalAssoc h g f)) (associator-route-base h g f) p)
```

The transferred statements below have precisely the boundaries of
`Triangle.Statement` and `Pentagon.Statement` in `InternalCoherence`.
Their comparison inputs are proof obligations, not replacements for those
boundaries by different choices.

```agda
universal-triangle-from-comparisons : {P A B C : CAT} (pAn : isAn P)
  (g : MAP P (Map B C)) (f : MAP P (Map A B))
  → Iso₂ (internalUnitʳ g) (compose-unitʳ pAn g)
  → Iso₂ (internalUnitˡ f) (compose-unitˡ pAn f)
  → Iso₂ (internalAssoc g (identityTerm B) f) (compose-assoc pAn g (identityTerm B) f)
  → Triangle.Statement g f
universal-triangle-from-comparisons pAn g f right-unit left-unit assoc =
  invIso (isoComp-cong (composeTerm-Iso₂ (idIso (idIso g)) left-unit) assoc) ∙
    (compose-triangle pAn g f ∙ composeTerm-Iso₂ right-unit (idIso (idIso f)))

universal-pentagon-from-comparisons : {P A B C D E : CAT} (pAn : isAn P)
  (k : MAP P (Map D E)) (h : MAP P (Map C D))
  (g : MAP P (Map B C)) (f : MAP P (Map A B))
  → Iso₂ (internalAssoc (composeTerm k h) g f) (compose-assoc pAn (composeTerm k h) g f)
  → Iso₂ (internalAssoc k h (composeTerm g f)) (compose-assoc pAn k h (composeTerm g f))
  → Iso₂ (internalAssoc k h g) (compose-assoc pAn k h g)
  → Iso₂ (internalAssoc k (composeTerm h g) f) (compose-assoc pAn k (composeTerm h g) f)
  → Iso₂ (internalAssoc h g f) (compose-assoc pAn h g f)
  → Pentagon.Statement k h g f
universal-pentagon-from-comparisons pAn k h g f a b c d e =
  let long-comparison = isoComp-cong
        (isoComp-cong (composeTerm-Iso₂ (idIso (idIso k)) e) d)
        (composeTerm-Iso₂ c (idIso (idIso f)))
  in invIso long-comparison ∙ (compose-pentagon pAn k h g f ∙ isoComp-cong b a)
```
