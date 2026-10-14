# The intermediate square of a cospan fiber

The pullback of the left fiber and the composite-right-leg fiber is
cartesian over the induced functor on pullbacks. The proof compares the
whole image cones, lifts their comparison through the target pullback,
and uses its controlled left projection for pullback cancellation.
No composition law for higher cone-action witnesses is assumed.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.Cospans.FiberInterchangeSquare
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Laws.PullbackStructure P
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Inverses as Inverses
open Inverses vocabulary terminal products productLaws composition vertical using (cancel-right; cancel-left; cancel-left-reflect)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap; cone-match-change; coneIso-swap; coneSwap-pre)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CompositeCones 𝒯 using (compositeCone; compositeConeIso; compositeCone-pre)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-inverse; inverse-composite; inverse-identity; pre-inverse)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting 𝒯 P using (pullback-reflect)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
import SCT.VolumeI.Chapter01.Section06.Cospans.ConeAction as Actions
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanAction as Normalized
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.FunctorCoherence as Coherence
open Coherence vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (right-unitor-comp)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-comp-at)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
import SCT.VolumeI.Chapter01.Section06.Cospans.Fibers as Fibers
import SCT.VolumeI.Chapter01.Section06.Cospans.FiberImages as Images
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting as Lifting
import SCT.VolumeI.Chapter01.Section06.Pasting.ComparisonCancellation as Cancellation
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.FramedEdgeCones as Edges
import SCT.VolumeI.Chapter01.Section06.Pasting.BaseChangeSquares as BaseChange
import SCT.VolumeI.Chapter01.Section06.PastingLemma as Pasting
import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange as ArrowChange
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange 𝒯 using (changeLeft)

import SCT.VolumeI.Chapter01.Section06.Cospans.FiberInterchangeProjections as Projections

module At {C D E C′ D′ E′ Γ : CAT}
  {f : MAP C E} {g : MAP D E} {f′ : MAP C′ E′} {g′ : MAP D′ E′}
  (F : CospanMap f g f′ g′) (x : MAP Γ (Pullback f′ g′)) where
  private
    module F = CospanMap F using (mapCone; pullbackMap; pullbackMap-β)
      renaming (left to u; right to v; base to w; leftSquare to α; rightSquare to β)
    module Fib = Fibers.At 𝒯 P F x
      using (family; left-family; right-family; base-family; matching;
        left-fiber; right-fiber; base-fiber; left-map; right-map;
        left-image-cone; right-image-cone; left-image; right-image; left-restriction)
    A = pullbackCone F.u Fib.left-family
    B = pullbackCone F.v Fib.right-family
    Z = pullbackCone F.w Fib.base-family
    target = pullbackCone f′ g′

  private
    module Projection = Projections.At 𝒯 P F x
      using (composite-cone; target-leg-fiber; target-leg-cone; to-base; base-computation; to-target; target-computation; target-square; target-square-isPullback; right-map; right-computation; intermediate; intermediate-cone; source-image; to-source; source-computation; source-square; source-square-isPullback; source-square-matching)
    open Projection
    module RightEdge = Edges.At 𝒯 F.v g′ F.β Fib.base-family using (edge; restrict-with-legs)

  private
    module LeftImage = Images.Along 𝒯 F.u Fib.left-family f F.w f′ Fib.base-family F.α (idIso Fib.base-family)
      using (value; left-normal)
    l = Cone.left intermediate-cone
    r = Cone.right intermediate-cone
    left-restricted = conePre l A
    composite-restricted = conePre r composite-cone

  intermediate-base-comparison :
    ConeIso (LeftImage.value left-restricted) (compositeCone g F.w composite-restricted)
  intermediate-base-comparison = coneIso-compose (compositeCone-pre g F.w r composite-cone)
    (coneIso-compose (coneIso-pre r base-computation)
      (coneIso-compose (coneIso-inverse (conePre-assoc r to-base Z))
        (coneIso-compose (cone-action Z (Cone.match intermediate-cone))
          (coneIso-inverse (Fib.left-restriction l)))))

  normalized-source : Cone f g intermediate
  normalized-source = record { left = Cone.left left-restricted ; right = Cone.left composite-restricted
    ; match = ConeIso.leftIso intermediate-base-comparison }

  source-normalization : ConeIso source-image normalized-source
  source-normalization = cone-match-change _ _ _ _ (calculation ⁻¹)
    where
    A₀ = comp-assoc l (Cone.left A) f
    B₀ = comp-assoc l Fib.left-map (Cone.left Z)
    C₀ = ConeIso.leftIso Fib.left-image ▷ l
    D₀ = comp-assoc r (Cone.left composite-cone) g
    E₀ = ConeIso.leftIso base-computation ▷ r
    F₀ = (comp-assoc r to-base (Cone.left Z)) ⁻¹
    G₀ = Cone.left Z ◁ Cone.match intermediate-cone
    L₀ = ConeIso.leftIso (Fib.left-restriction l)
    inner-inverse : ((C₀ ∙ B₀ ⁻¹) ⁻¹) =₂ (B₀ ∙ C₀ ⁻¹)
    inner-inverse = isoComp-cong (inverse-inverse B₀) (idIso (C₀ ⁻¹)) ∙ inverse-composite C₀ (B₀ ⁻¹)
    left-inverse : (L₀ ⁻¹) =₂ ((B₀ ∙ C₀ ⁻¹) ∙ A₀ ⁻¹)
    left-inverse = isoComp-cong inner-inverse (inverse-inverse (A₀ ⁻¹)) ∙
      inverse-composite ((A₀ ⁻¹) ⁻¹) (C₀ ∙ B₀ ⁻¹)
    H₀ = D₀ ∙ (E₀ ∙ F₀)
    calculation : Cone.match normalized-source =₂ Cone.match source-image
    calculation =
      (isoComp-assoc-at (H₀ ∙ (G₀ ∙ B₀)) (C₀ ⁻¹) (A₀ ⁻¹)) ⁻¹ ∙
      (isoComp-cong (isoComp-assoc-at H₀ G₀ B₀) (idIso (C₀ ⁻¹ ∙ A₀ ⁻¹)) ∙
      ((isoComp-assoc-at (H₀ ∙ G₀) B₀ (C₀ ⁻¹ ∙ A₀ ⁻¹)) ⁻¹ ∙
      (isoComp-cong (idIso (H₀ ∙ G₀)) (isoComp-assoc-at B₀ (C₀ ⁻¹) (A₀ ⁻¹)) ∙
      ((isoComp-assoc-at H₀ G₀ ((B₀ ∙ C₀ ⁻¹) ∙ A₀ ⁻¹)) ⁻¹ ∙
      (isoComp-cong (idIso H₀) (isoComp-cong (idIso G₀) left-inverse) ∙
      ((isoComp-assoc-at D₀ (E₀ ∙ F₀) (G₀ ∙ L₀ ⁻¹)) ⁻¹ ∙
        isoComp-cong (idIso D₀) ((isoComp-assoc-at E₀ F₀ (G₀ ∙ L₀ ⁻¹)) ⁻¹)))))))


  private
    module Image = Normalized.Action 𝒯 P F using (normalized; left-change; right-change; module Normalization)

  normalized-target : Cone f′ g′ intermediate
  normalized-target = compositeCone Fib.left-family f′ (coneSwap (RightEdge.edge composite-restricted))

  intermediate-image-comparison : ConeIso (Image.normalized normalized-source) normalized-target
  intermediate-image-comparison = record
    { leftIso = (Fib.left-family ◁ ConeIso.rightIso intermediate-base-comparison) ∙ Cone.match left-restricted
    ; rightIso = idIso (F.v ∘ Cone.left composite-restricted)
    ; compatible = isoComp-cong ((postWhisker-idIso g′ _) ⁻¹) (idIso _) ∙
        ((isoComp-unitˡ-at _) ⁻¹ ∙ final) }
    where
    δ = ConeIso.leftIso intermediate-base-comparison
    ε = ConeIso.rightIso intermediate-base-comparison
    μ = Cone.match left-restricted
    AL = Image.left-change normalized-source
    BR = Image.right-change normalized-source
    M = F.w ◁ δ
    J = f′ ◁ μ
    U = f′ ◁ (Fib.left-family ◁ ε)
    T₀ = comp-assoc (Cone.right left-restricted) Fib.left-family f′
    T₁ = comp-assoc (Cone.right composite-restricted) Fib.left-family f′
    MR = Cone.match (compositeCone g F.w composite-restricted)
    ML = Cone.match (LeftImage.value left-restricted)
    ρ = Cone.match (RightEdge.edge composite-restricted)
    N = Cone.match normalized-target
    rest = M ∙ AL
    left-matching : ML =₂ (T₀ ⁻¹ ∙ (J ∙ AL ⁻¹))
    left-matching = isoComp-cong
      (isoComp-unitˡ-at (T₀ ⁻¹) ∙
        isoComp-cong (preWhisker-idIso Fib.base-family (Cone.right left-restricted)) (idIso (T₀ ⁻¹)))
      (idIso (J ∙ AL ⁻¹))
    right-matching : ρ =₂ (MR ∙ BR)
    right-matching = (isoComp-assoc-at (Cone.match composite-restricted)
        ((comp-assoc (Cone.left composite-restricted) g F.w) ⁻¹) BR) ⁻¹ ∙
      (isoComp-cong (idIso (Cone.match composite-restricted))
        (cancel-left (comp-assoc (Cone.left composite-restricted) g F.w)
          ((F.β ▷ Cone.left composite-restricted) ∙ (comp-assoc (Cone.left composite-restricted) F.v g′) ⁻¹))) ⁻¹
    transported : ((Fib.base-family ◁ ε) ∙ T₀ ⁻¹) =₂ (T₁ ⁻¹ ∙ U)
    transported = (move-square T₁ (Fib.base-family ◁ ε) U T₀
      (postWhisker-comp-at ε Fib.left-family f′)) ⁻¹
    middle : (MR ∙ rest) =₂ (T₁ ⁻¹ ∙ (U ∙ J))
    middle = isoComp-assoc-at (T₁ ⁻¹) U J ∙
      (isoComp-cong transported (idIso J) ∙
      ((isoComp-assoc-at (Fib.base-family ◁ ε) (T₀ ⁻¹) J) ⁻¹ ∙
      (isoComp-cong (idIso (Fib.base-family ◁ ε))
        (isoComp-cong (idIso (T₀ ⁻¹))
          (isoComp-unitʳ-at J ∙ isoComp-cong (idIso J) (isoComp-inverseˡ-at AL)) ∙
          (isoComp-cong (idIso (T₀ ⁻¹)) (isoComp-assoc-at J (AL ⁻¹) AL) ∙
          (isoComp-assoc-at (T₀ ⁻¹) (J ∙ AL ⁻¹) AL ∙ isoComp-cong left-matching (idIso AL)))) ∙
      (isoComp-assoc-at (Fib.base-family ◁ ε) ML AL ∙
      (isoComp-cong (ConeIso.compatible intermediate-base-comparison) (idIso AL) ∙
        (isoComp-assoc-at MR M AL) ⁻¹)))))
    calculation : (N ∙ (U ∙ J)) =₂ (BR ⁻¹ ∙ rest)
    calculation = cancel-left-reflect ρ
      ((isoComp-cong (idIso MR) (cancel-inverse BR rest) ∙
        (isoComp-assoc-at MR BR (BR ⁻¹ ∙ rest) ∙
          isoComp-cong right-matching (idIso (BR ⁻¹ ∙ rest)))) ⁻¹ ∙
      (middle ⁻¹ ∙
        (cancel-inverse ρ (T₁ ⁻¹ ∙ (U ∙ J)) ∙
          isoComp-cong (idIso ρ) (isoComp-assoc-at (ρ ⁻¹) (T₁ ⁻¹) (U ∙ J)))))
    final = calculation ∙ isoComp-cong (idIso N)
      (postWhisker-isoComp-at f′ (Fib.left-family ◁ ε) μ)


  intermediate-map : MAP intermediate target-leg-fiber
  intermediate-map = right-map ∘ r

  intermediate-right-computation : ConeIso (conePre intermediate-map target-leg-cone)
    (RightEdge.edge composite-restricted)
  intermediate-right-computation = coneIso-adjust raw (ConeIso.leftIso raw)
    ((ConeIso.rightIso right-computation ▷ r) ∙ (comp-assoc r right-map (Cone.right target-leg-cone)) ⁻¹)
    (idIso _) (isoComp-unitˡ-at _)
    where
    raw = coneIso-compose (RightEdge.restrict-with-legs r composite-cone)
      (coneIso-compose (coneIso-pre r right-computation)
        (coneIso-inverse (conePre-assoc r right-map target-leg-cone)))

  intermediate-target-computation : ConeIso (conePre (to-target ∘ intermediate-map) target) normalized-target
  intermediate-target-computation =
    coneIso-compose (compositeConeIso Fib.left-family f′ (coneIso-swap intermediate-right-computation))
      (coneIso-compose (compositeConeIso Fib.left-family f′ (coneSwap-pre intermediate-map target-leg-cone))
        (coneIso-compose (compositeCone-pre Fib.left-family f′ intermediate-map (coneSwap target-leg-cone))
          (coneIso-compose (coneIso-pre intermediate-map target-computation)
            (coneIso-inverse (conePre-assoc intermediate-map to-target target)))))

  private
    module Action = Actions.Action 𝒯 P F using (map-iso-with-legs; map-pre-with-legs)

  intermediate-source-computation : ConeIso (conePre (F.pullbackMap ∘ to-source) target) normalized-target
  intermediate-source-computation = coneIso-compose intermediate-image-comparison
    (coneIso-compose (coneIso-inverse (Image.Normalization.comparison normalized-source))
      (coneIso-compose (Action.map-iso-with-legs source-normalization)
        (coneIso-compose (Action.map-iso-with-legs source-computation)
          (coneIso-compose (coneIso-inverse (Action.map-pre-with-legs to-source (pullbackCone f g)))
            (coneIso-compose (coneIso-pre to-source F.pullbackMap-β)
              (coneIso-inverse (conePre-assoc to-source F.pullbackMap target)))))))



  private
    κ = ConeIso.leftIso F.pullbackMap-β
    ζ = ConeIso.leftIso source-computation
    μ = Cone.match left-restricted
    ε = ConeIso.rightIso intermediate-base-comparison
    ν₀ = ConeIso.rightIso intermediate-right-computation
    ν = ε ⁻¹ ∙ ν₀
    I = (F.u ◁ ζ) ∙ (comp-assoc to-source (Cone.left (pullbackCone f g)) F.u ∙
      ((κ ▷ to-source) ∙ (comp-assoc to-source F.pullbackMap (Cone.left target)) ⁻¹))
    module SourceChange = ArrowChange.ChangeLeft 𝒯 P (κ ⁻¹) Fib.left-family using (preserve)

  intermediate-outer : Cone (Cone.left target ∘ F.pullbackMap) Fib.left-family intermediate
  intermediate-outer = changeLeft (κ ⁻¹) source-square
  intermediate-outer-isPullback : IsPullback intermediate-outer
  intermediate-outer-isPullback = SourceChange.preserve source-square source-square-isPullback

  private
    Q = compositeCone F.pullbackMap (Cone.left target) intermediate-outer
    T = conePre intermediate-map target-square

  intermediate-outer-matching : Cone.match Q =₂ (μ ∙ I)
  intermediate-outer-matching =
    isoComp-cong (idIso μ) (isoComp-assoc-at (F.u ◁ ζ) A₀ (B₀ ∙ C₀)) ∙
    (isoComp-assoc-at μ ((F.u ◁ ζ) ∙ A₀) (B₀ ∙ C₀) ∙
    (isoComp-assoc-at (μ ∙ ((F.u ◁ ζ) ∙ A₀)) B₀ C₀ ∙
      isoComp-cong (isoComp-cong source-match inverse-whisker) (idIso C₀)))
    where
    A₀ = comp-assoc to-source (Cone.left (pullbackCone f g)) F.u
    B₀ = κ ▷ to-source
    C₀ = (comp-assoc to-source F.pullbackMap (Cone.left target)) ⁻¹
    source-match = source-square-matching
    inverse-whisker : ((κ ⁻¹ ▷ to-source) ⁻¹) =₂ B₀
    inverse-whisker = inverse-inverse B₀ ∙ (＝-inv ◁ pre-inverse κ to-source)

  intermediate-total-comparison : ConeIso (conePre (to-target ∘ intermediate-map) target)
    (conePre (F.pullbackMap ∘ to-source) target)
  intermediate-total-comparison = coneIso-compose (coneIso-inverse intermediate-source-computation)
    intermediate-target-computation

  private
    module IntermediateLift = Lifting.Lift 𝒯 P (to-target ∘ intermediate-map)
      (F.pullbackMap ∘ to-source) intermediate-total-comparison using (lift; left-image; right-image; comparison-image)
  intermediate-identification : (to-target ∘ intermediate-map) =₁ (F.pullbackMap ∘ to-source)
  intermediate-identification = IntermediateLift.lift
  open IntermediateLift public using () renaming
    (left-image to intermediate-left-image; right-image to intermediate-right-image;
     comparison-image to intermediate-comparison-image)


  intermediate-source-projection : ConeIso.leftIso intermediate-source-computation =₂
    ((Fib.left-family ◁ ε) ∙ Cone.match Q)
  intermediate-source-projection = isoComp-cong (idIso (Fib.left-family ◁ ε)) (intermediate-outer-matching ⁻¹) ∙
    (isoComp-assoc-at (Fib.left-family ◁ ε) μ I ∙
      isoComp-cong (idIso ((Fib.left-family ◁ ε) ∙ μ))
        (isoComp-unitˡ-at I ∙ isoComp-cong (inverse-identity (F.u ∘ Cone.left left-restricted) ∙ (＝-inv ◁ Image.Normalization.comparison-left normalized-source))
          (isoComp-unitˡ-at I ∙ isoComp-cong (postWhisker-idIso F.u (Cone.left left-restricted))
            (isoComp-cong (idIso (F.u ◁ ζ))
              (isoComp-cong (inverse-inverse (comp-assoc to-source (Cone.left (pullbackCone f g)) F.u))
                (idIso _))))))

  intermediate-target-projection : ConeIso.leftIso intermediate-target-computation =₂
    ((Fib.left-family ◁ ν₀) ∙ Cone.match T)
  intermediate-target-projection = isoComp-cong (idIso (Fib.left-family ◁ ν₀))
    (isoComp-unitˡ-at (Cone.match T) ∙
      isoComp-cong (postWhisker-idIso Fib.left-family (Cone.right target-leg-cone ∘ intermediate-map))
        (idIso (Cone.match T)))

  intermediate-factor-computation : ConeIso (conePre intermediate-map target-square) Q
  intermediate-factor-computation = record
    { leftIso = intermediate-identification ; rightIso = ν
    ; compatible = cancel-left-reflect (Fib.left-family ◁ ε)
        (right-cancellation ⁻¹ ∙ left-cancellation) }
    where
    L₀ = Fib.left-family ◁ ε
    R₀ = Fib.left-family ◁ ν₀
    W = Cone.left target ◁ intermediate-identification
    QM = Cone.match Q
    TM = Cone.match T
    projection : W =₂ ((L₀ ∙ QM) ⁻¹ ∙ (R₀ ∙ TM))
    projection = isoComp-cong (＝-inv ◁ intermediate-source-projection) intermediate-target-projection ∙
      IntermediateLift.left-image
    left-cancellation : (L₀ ∙ (QM ∙ W)) =₂ (R₀ ∙ TM)
    left-cancellation = cancel-inverse (L₀ ∙ QM) (R₀ ∙ TM) ∙
      (isoComp-cong (idIso (L₀ ∙ QM)) projection ∙ (isoComp-assoc-at L₀ QM W) ⁻¹)
    right-cancellation : (L₀ ∙ ((Fib.left-family ◁ ν) ∙ TM)) =₂ (R₀ ∙ TM)
    right-cancellation = isoComp-cong
      ((postWhisker Fib.left-family ◁ cancel-inverse ε ν₀) ∙
        (postWhisker-isoComp-at Fib.left-family ε ν) ⁻¹)
      (idIso TM) ∙ (isoComp-assoc-at L₀ (Fib.left-family ◁ ν) TM) ⁻¹

  private
    module Intermediate = Cancellation.At 𝒯 P F.pullbackMap (Cone.left target) Fib.left-family
      target-square target-square-isPullback intermediate-outer intermediate-outer-isPullback
      intermediate-map intermediate-factor-computation using (square; square-isPullback)

  intermediate-square : Cone F.pullbackMap to-target intermediate
  intermediate-square = Intermediate.square
  intermediate-square-isPullback : IsPullback intermediate-square
  intermediate-square-isPullback = Intermediate.square-isPullback

```
