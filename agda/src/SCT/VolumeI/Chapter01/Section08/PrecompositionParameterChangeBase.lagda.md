# Restriction and successive parameter changes

We evaluate the pasted separation squares using the square-projection
calculus from Section 1.3. This retains the chosen currying beta witness,
so that the comparison applies to the actual precomposition functor.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.RetainedCompositionParameterChange as Project
import SCT.VolumeI.Chapter01.Section02.Structural as Structural
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section08.PrecompositionParameterChangeBase
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section03.Compatibility 𝒯 M using (slice-comparison)
open import SCT.VolumeI.Chapter01.Section05.InverseCalculus 𝒯 using (pre-inverse)
open import SCT.VolumeI.Chapter01.Section08.EvaluationSquares 𝒯 using (cancel-evaluation-route; cancel-evaluation-pairs; append-five; append-square; compose-evaluated-pasting)
open import SCT.VolumeI.Chapter01.Section05.ComparisonSquares 𝒯 using (post-square)
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section08.ProductMixedSubstitution 𝒯 M using (separate-substitution)
open import SCT.VolumeI.Chapter01.Section03.ParameterSquarePasting 𝒯 using (paste)
open import SCT.VolumeI.Chapter01.Section03.SubstitutionCoherence 𝒯 M using (mapUncurry-pre-iterated)
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
  uk = mapUncurry-pre (mapPre f) k
  qk = mapPre-uncurry f k

  module Pasted = Project.EvaluationPaste 𝒯 M HA KA HB KB LX LY LZ
    mapEval (mapUncurry (mapPre f)) (mapUncurry k) (mapUncurry (mapPre f ∘ k))
    (invIso β) (idIso (mapUncurry k)) (invIso uk) Sk Sh qk

  t = invIso (comp-assoc LY KB mapEval)
  d = mapEval ◁ Sk
  c₀ = comp-assoc KA LZ mapEval
  b₀ = β ▷ KA
  right-tail = invIso uk ∙ ((invIso β ▷ KA) ∙ invIso c₀)

  abstract
    square : =₂
      ((((idIso (mapUncurry k) ▷ LY) ∙ t) ∙ d))
      (qk ∙ right-tail)

    square = invIso normalize-right ∙ normalize-left
      where
      normalize-left : =₂ (((idIso (mapUncurry k) ▷ LY) ∙ t) ∙ d) (t ∙ d)
      normalize-left = isoComp-cong
        (isoComp-unitˡ-at t ∙ isoComp-cong (preWhisker-idIso (mapUncurry k) LY) (idIso t)) (idIso d)
      normalize-right : =₂ (qk ∙ right-tail) (t ∙ d)
      normalize-right = cancel-evaluation-route (t ∙ d) c₀ b₀ uk ∙
        isoComp-cong (invIso (isoComp-assoc-at t d (c₀ ∙ (b₀ ∙ uk))))
          (isoComp-cong (idIso (invIso uk))
            (isoComp-cong (pre-inverse β KA) (idIso (invIso c₀))))

  abstract
    pasted-evaluation : =₂ (Pasted.target-evaluation ∙ (mapEval ◁ paste Sk Sh))
      (Pasted.evaluation-action ∙ Pasted.source-evaluation)

    pasted-evaluation = Pasted.project-paste square

  KHA = productMap (k ∘ h) (id A)
  KHB = productMap (k ∘ h) (id B)
  κA = slice-comparison {C = A} k h
  κB = slice-comparison {C = B} k h
  e = mapEval {C = B} {D = E}
  U = mapUncurry (mapPre {D = E} f)
  u = mapUncurry-pre (mapPre f ∘ k) h
  v = mapUncurry-pre (mapPre f) (k ∘ h)
  τ = mapUncurryIso (comp-assoc h k (mapPre f))
  w = mapUncurry-pre k h
  a₁ = uk ▷ HA
  a₂ = comp-assoc HA KA U
  a₃ = β ▷ (KA ∘ HA)
  a₄ = comp-assoc (KA ∘ HA) LZ e
  z = a₄ ∙ (a₃ ∙ (a₂ ∙ (a₁ ∙ u)))

  abstract
    source-endpoint : =₂ (Pasted.source-evaluation ∙ z) u

    source-endpoint = cancel-evaluation-pairs a₁ a₂ a₃ a₄ u ∙
      isoComp-cong
        (isoComp-cong
          (isoComp-cong (pre-inverse uk HA) (idIso (invIso a₂)))
          (isoComp-cong (pre-inverse β (KA ∘ HA)) (idIso (invIso a₄))))
        (idIso z)

  composite-input = comp-assoc KHA LZ e ∙ ((β ▷ KHA) ∙ (v ∙ τ))
  input-action = e ◁ (LZ ◁ κA)

  abstract
    input-square : =₂
      (comp-assoc KHA LZ e ∙ ((β ▷ KHA) ∙ (U ◁ κA)))
      (input-action ∙ (a₄ ∙ a₃))

    input-square = isoComp-assoc-at input-action a₄ a₃ ∙
      (isoComp-cong (postWhisker-comp-at κA LZ e) (idIso a₃) ∙
      (invIso (isoComp-assoc-at (comp-assoc KHA LZ e) ((e ∘ LZ) ◁ κA) a₃) ∙
        isoComp-cong (idIso (comp-assoc KHA LZ e)) (interchange-at β κA)))

  abstract
    input-endpoint : =₂ composite-input (input-action ∙ z)

    input-endpoint =
      isoComp-cong (idIso input-action) (isoComp-assoc-at a₄ a₃ (a₂ ∙ (a₁ ∙ u))) ∙
      (isoComp-assoc-at input-action (a₄ ∙ a₃) (a₂ ∙ (a₁ ∙ u)) ∙
      (isoComp-cong input-square (idIso (a₂ ∙ (a₁ ∙ u))) ∙
      (invIso (isoComp-assoc-at (comp-assoc KHA LZ e) ((β ▷ KHA) ∙ (U ◁ κA)) (a₂ ∙ (a₁ ∙ u))) ∙
      (isoComp-cong (idIso (comp-assoc KHA LZ e))
        (invIso (isoComp-assoc-at (β ▷ KHA) (U ◁ κA) (a₂ ∙ (a₁ ∙ u)))) ∙
        isoComp-cong (idIso (comp-assoc KHA LZ e))
          (isoComp-cong (idIso (β ▷ KHA)) (mapUncurry-pre-iterated (mapPre f) k h))))))

  output-associator = invIso (comp-assoc LX KHB e)
  output-action = e ◁ (κB ▷ LX)
  abstract
    output-endpoint : =₂
      ((w ▷ LX) ∙ (output-associator ∙ output-action)) Pasted.target-evaluation

    output-endpoint = invIso normalize-target ∙
      (isoComp-cong restricted-cancellation (idIso final-associator) ∙
      (invIso (isoComp-assoc-at (w ▷ LX) ((e ◁ κB) ▷ LX) final-associator) ∙
        isoComp-cong (idIso (w ▷ LX))
          (move-square (comp-assoc LX KHB e) ((e ◁ κB) ▷ LX) output-action
            (comp-assoc LX (KB ∘ HB) e) (whisker-mixed-at κB LX e))))
      where
      final-associator : =₁ (e ∘ ((KB ∘ HB) ∘ LX)) ((e ∘ (KB ∘ HB)) ∘ LX)
      final-associator = invIso (comp-assoc LX (KB ∘ HB) e)
      before : =₁ (e ∘ (KB ∘ HB)) ((e ∘ KB) ∘ HB)
      before = invIso (comp-assoc HB KB e)
      image-cancellation : =₂ ((e ◁ invIso κB) ∙ (e ◁ κB)) (idIso (e ∘ (KB ∘ HB)))
      image-cancellation = postWhisker-idIso e (KB ∘ HB) ∙
        ((postWhisker e ◁ isoComp-inverseˡ-at κB) ∙
          invIso (postWhisker-isoComp-at e (invIso κB) κB))
      cancellation : =₂ (w ∙ (e ◁ κB)) before
      cancellation = isoComp-unitʳ-at before ∙
        (isoComp-cong (idIso before) image-cancellation ∙
          isoComp-assoc-at before (e ◁ invIso κB) (e ◁ κB))
      restricted-cancellation : =₂ ((w ▷ LX) ∙ ((e ◁ κB) ▷ LX)) (before ▷ LX)
      restricted-cancellation = (preWhisker LX ◁ cancellation) ∙
        invIso (preWhisker-isoComp-at w (e ◁ κB) LX)
      normalize-target : =₂ Pasted.target-evaluation ((before ▷ LX) ∙ final-associator)
      normalize-target = isoComp-cong
        (preWhisker LX ◁ (isoComp-unitˡ-at before ∙
          isoComp-cong (preWhisker-idIso (mapUncurry k) HB) (idIso before)))
        (idIso final-associator)

```
