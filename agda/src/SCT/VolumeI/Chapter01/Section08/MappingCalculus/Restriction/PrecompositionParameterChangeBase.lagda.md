# Restriction and successive parameter changes

We evaluate the pasted separation squares using the square-projection
calculus from Section 1.4. This retains the chosen currying beta witness,
so that the comparison applies to the actual precomposition functor.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.RetainedCompositionParameterChange as Project
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.PrecompositionParameterChangeBase
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Substitution.Compatibility 𝒯 M using (slice-comparison)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse)
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.EvaluationSquares 𝒯 using (cancel-evaluation-route; cancel-evaluation-pairs; append-five; append-square; compose-evaluated-pasting)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯 using (post-square)
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductMixedSubstitution 𝒯 M using (separate-substitution)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ParameterSquarePasting 𝒯 using (paste)
open import SCT.VolumeI.Chapter01.Section04.Substitution.SubstitutionCoherence 𝒯 M using (mapUncurry-restrict-iterated)
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-comp-at; whisker-mixed-at)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

module ParameterChange {X Y A B E : CAT}
  (f : MAP A B) (k : MAP Y (Map B E)) (h : MAP X Y) where
  Z = Map B E
  HA = productMap h (id A)
  HB = productMap h (id B)
  KA = productMap k (id A)
  KB = productMap k (id B)
  LX = productRestriction X f
  LY = productRestriction Y f
  LZ = productRestriction Z f
  Sh = productMap-separate h f
  Sk = productMap-separate k f
  β = mapPre-β {D = E} f
  uk = mapUncurry-restrict (mapPre f) k
  qk = mapPre-uncurry f k

  module Pasted = Project.EvaluationPaste 𝒯 M HA KA HB KB LX LY LZ
    mapEval (mapUncurry (mapPre f)) (mapUncurry k) (mapUncurry (mapPre f ∘ k))
    (β ⁻¹) (idIso (mapUncurry k)) (uk ⁻¹) Sk Sh qk

  t = (comp-assoc LY KB mapEval) ⁻¹
  d = mapEval ◁ Sk
  c₀ = comp-assoc KA LZ mapEval
  b₀ = β ▷ KA
  right-tail = uk ⁻¹ ∙ ((β ⁻¹ ▷ KA) ∙ c₀ ⁻¹)

  abstract
    square :
      ((((idIso (mapUncurry k) ▷ LY) ∙ t) ∙ d)) =₂
      (qk ∙ right-tail)

    square = normalize-right ⁻¹ ∙ normalize-left
      where
      normalize-left : (((idIso (mapUncurry k) ▷ LY) ∙ t) ∙ d) =₂ (t ∙ d)
      normalize-left = isoComp-cong
        (isoComp-unitˡ-at t ∙ isoComp-cong (preWhisker-idIso (mapUncurry k) LY) (idIso t)) (idIso d)
      normalize-right : (qk ∙ right-tail) =₂ (t ∙ d)
      normalize-right = cancel-evaluation-route (t ∙ d) c₀ b₀ uk ∙
        isoComp-cong ((isoComp-assoc-at t d (c₀ ∙ (b₀ ∙ uk))) ⁻¹)
          (isoComp-cong (idIso (uk ⁻¹))
            (isoComp-cong (pre-inverse β KA) (idIso (c₀ ⁻¹))))

  abstract
    pasted-evaluation : (Pasted.target-evaluation ∙ (mapEval ◁ paste Sk Sh)) =₂
      (Pasted.evaluation-action ∙ Pasted.source-evaluation)

    pasted-evaluation = Pasted.project-paste square

  KHA = productMap (k ∘ h) (id A)
  KHB = productMap (k ∘ h) (id B)
  κA = slice-comparison {C = A} k h
  κB = slice-comparison {C = B} k h
  e = mapEval {C = B} {D = E}
  U = mapUncurry (mapPre {D = E} f)
  u = mapUncurry-restrict (mapPre f ∘ k) h
  v = mapUncurry-restrict (mapPre f) (k ∘ h)
  τ = mapUncurryIso (comp-assoc h k (mapPre f))
  w = mapUncurry-restrict k h
  a₁ = uk ▷ HA
  a₂ = comp-assoc HA KA U
  a₃ = β ▷ (KA ∘ HA)
  a₄ = comp-assoc (KA ∘ HA) LZ e
  z = a₄ ∙ (a₃ ∙ (a₂ ∙ (a₁ ∙ u)))

  abstract
    source-endpoint : (Pasted.source-evaluation ∙ z) =₂ u

    source-endpoint = cancel-evaluation-pairs a₁ a₂ a₃ a₄ u ∙
      isoComp-cong
        (isoComp-cong
          (isoComp-cong (pre-inverse uk HA) (idIso (a₂ ⁻¹)))
          (isoComp-cong (pre-inverse β (KA ∘ HA)) (idIso (a₄ ⁻¹))))
        (idIso z)

  composite-input = comp-assoc KHA LZ e ∙ ((β ▷ KHA) ∙ (v ∙ τ))
  input-action = e ◁ (LZ ◁ κA)

  abstract
    input-square :
      (comp-assoc KHA LZ e ∙ ((β ▷ KHA) ∙ (U ◁ κA))) =₂
      (input-action ∙ (a₄ ∙ a₃))

    input-square = isoComp-assoc-at input-action a₄ a₃ ∙
      (isoComp-cong (postWhisker-comp-at κA LZ e) (idIso a₃) ∙
      ((isoComp-assoc-at (comp-assoc KHA LZ e) ((e ∘ LZ) ◁ κA) a₃) ⁻¹ ∙
        isoComp-cong (idIso (comp-assoc KHA LZ e)) (interchange-at β κA)))

  abstract
    input-endpoint : composite-input =₂ (input-action ∙ z)

    input-endpoint =
      isoComp-cong (idIso input-action) (isoComp-assoc-at a₄ a₃ (a₂ ∙ (a₁ ∙ u))) ∙
      (isoComp-assoc-at input-action (a₄ ∙ a₃) (a₂ ∙ (a₁ ∙ u)) ∙
      (isoComp-cong input-square (idIso (a₂ ∙ (a₁ ∙ u))) ∙
      ((isoComp-assoc-at (comp-assoc KHA LZ e) ((β ▷ KHA) ∙ (U ◁ κA)) (a₂ ∙ (a₁ ∙ u))) ⁻¹ ∙
      (isoComp-cong (idIso (comp-assoc KHA LZ e))
        ((isoComp-assoc-at (β ▷ KHA) (U ◁ κA) (a₂ ∙ (a₁ ∙ u))) ⁻¹) ∙
        isoComp-cong (idIso (comp-assoc KHA LZ e))
          (isoComp-cong (idIso (β ▷ KHA)) (mapUncurry-restrict-iterated (mapPre f) k h))))))

  output-associator = (comp-assoc LX KHB e) ⁻¹
  output-action = e ◁ (κB ▷ LX)
  abstract
    output-endpoint :
      ((w ▷ LX) ∙ (output-associator ∙ output-action)) =₂ Pasted.target-evaluation

    output-endpoint = normalize-target ⁻¹ ∙
      (isoComp-cong restricted-cancellation (idIso final-associator) ∙
      ((isoComp-assoc-at (w ▷ LX) ((e ◁ κB) ▷ LX) final-associator) ⁻¹ ∙
        isoComp-cong (idIso (w ▷ LX))
          (move-square (comp-assoc LX KHB e) ((e ◁ κB) ▷ LX) output-action
            (comp-assoc LX (KB ∘ HB) e) (whisker-mixed-at κB LX e))))
      where
      final-associator : (e ∘ ((KB ∘ HB) ∘ LX)) =₁ ((e ∘ (KB ∘ HB)) ∘ LX)
      final-associator = (comp-assoc LX (KB ∘ HB) e) ⁻¹
      before : (e ∘ (KB ∘ HB)) =₁ ((e ∘ KB) ∘ HB)
      before = (comp-assoc HB KB e) ⁻¹
      image-cancellation : ((e ◁ κB ⁻¹) ∙ (e ◁ κB)) =₂ (idIso (e ∘ (KB ∘ HB)))
      image-cancellation = postWhisker-idIso e (KB ∘ HB) ∙
        ((postWhisker e ◁ isoComp-inverseˡ-at κB) ∙
          (postWhisker-isoComp-at e (κB ⁻¹) κB) ⁻¹)
      cancellation : (w ∙ (e ◁ κB)) =₂ before
      cancellation = isoComp-unitʳ-at before ∙
        (isoComp-cong (idIso before) image-cancellation ∙
          isoComp-assoc-at before (e ◁ κB ⁻¹) (e ◁ κB))
      restricted-cancellation : ((w ▷ LX) ∙ ((e ◁ κB) ▷ LX)) =₂ (before ▷ LX)
      restricted-cancellation = (preWhisker LX ◁ cancellation) ∙
        (preWhisker-isoComp-at w (e ◁ κB) LX) ⁻¹
      normalize-target : Pasted.target-evaluation =₂ ((before ▷ LX) ∙ final-associator)
      normalize-target = isoComp-cong
        (preWhisker LX ◁ (isoComp-unitˡ-at before ∙
          isoComp-cong (preWhisker-idIso (mapUncurry k) HB) (idIso before)))
        (idIso final-associator)

```
