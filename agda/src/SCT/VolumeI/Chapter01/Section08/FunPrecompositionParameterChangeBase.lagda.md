# Functor-category restriction and successive parameter changes

We evaluate the pasted separation squares using the square-projection
calculus from Section 1.3. This retains the chosen currying beta witness,
so that the comparison applies to the actual precomposition functor.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section03.RetainedCompositionParameterChange as Project
import SCT.VolumeI.Chapter01.Section02.Structural as Structural
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section08.FunPrecompositionParameterChangeBase
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section06.Setup 𝒯 M ℱ hiding (slice-comparison)
open import SCT.VolumeI.Chapter01.Section03.Compatibility 𝒯 M using (slice-comparison)
open import SCT.VolumeI.Chapter01.Section05.InverseCalculus 𝒯 using (pre-inverse)
open import SCT.VolumeI.Chapter01.Section08.EvaluationSquares 𝒯 using (cancel-evaluation-route; cancel-evaluation-pairs; append-five; append-square; compose-evaluated-pasting)
open import SCT.VolumeI.Chapter01.Section05.ComparisonSquares 𝒯 using (post-square)
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section08.ProductMixedSubstitution 𝒯 M using (separate-substitution)
open import SCT.VolumeI.Chapter01.Section03.ParameterSquarePasting 𝒯 using (paste)
open import SCT.VolumeI.Chapter01.Section06.SubstitutionCoherence 𝒯 M ℱ using (funUncurry-pre-iterated)
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-comp-at; whisker-mixed-at)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

module ParameterChange {X Y A B E : CAT}
  (f : MAP A B) (k : MAP Y (Fun B E)) (h : MAP X Y) where
  Z = Fun B E
  HA = productMap h (id A)
  HB = productMap h (id B)
  KA = productMap k (id A)
  KB = productMap k (id B)
  LX = productRestriction X f
  LY = productRestriction Y f
  LZ = productRestriction Z f
  Sh = productMap-separate h f
  Sk = productMap-separate k f
  β = funPre-β {D = E} f
  uk = funUncurry-pre (funPre f) k
  qk = funPre-uncurry f k

  module Pasted = Project.EvaluationPaste 𝒯 M HA KA HB KB LX LY LZ
    funEval (funUncurry (funPre f)) (funUncurry k) (funUncurry (funPre f ∘ k))
    (invIso β) (idIso (funUncurry k)) (invIso uk) Sk Sh qk

  t = invIso (comp-assoc LY KB funEval)
  d = funEval ◁ Sk
  c₀ = comp-assoc KA LZ funEval
  b₀ = β ▷ KA
  right-tail = invIso uk ∙ ((invIso β ▷ KA) ∙ invIso c₀)

  abstract
    square : Iso₂
      ((((idIso (funUncurry k) ▷ LY) ∙ t) ∙ d))
      (qk ∙ right-tail)

    square = invIso normalize-right ∙ normalize-left
      where
      normalize-left : Iso₂ (((idIso (funUncurry k) ▷ LY) ∙ t) ∙ d) (t ∙ d)
      normalize-left = isoComp-cong
        (isoComp-unitˡ-at t ∙ isoComp-cong (preWhisker-idIso (funUncurry k) LY) (idIso t)) (idIso d)
      normalize-right : Iso₂ (qk ∙ right-tail) (t ∙ d)
      normalize-right = cancel-evaluation-route (t ∙ d) c₀ b₀ uk ∙
        isoComp-cong (invIso (isoComp-assoc-at t d (c₀ ∙ (b₀ ∙ uk))))
          (isoComp-cong (idIso (invIso uk))
            (isoComp-cong (pre-inverse β KA) (idIso (invIso c₀))))

  abstract
    pasted-evaluation : Iso₂ (Pasted.target-evaluation ∙ (funEval ◁ paste Sk Sh))
      (Pasted.evaluation-action ∙ Pasted.source-evaluation)

    pasted-evaluation = Pasted.project-paste square

  KHA = productMap (k ∘ h) (id A)
  KHB = productMap (k ∘ h) (id B)
  κA = slice-comparison {C = A} k h
  κB = slice-comparison {C = B} k h
  e = funEval {C = B} {D = E}
  U = funUncurry (funPre {D = E} f)
  u = funUncurry-pre (funPre f ∘ k) h
  v = funUncurry-pre (funPre f) (k ∘ h)
  τ = funUncurryIso (comp-assoc h k (funPre f))
  w = funUncurry-pre k h
  a₁ = uk ▷ HA
  a₂ = comp-assoc HA KA U
  a₃ = β ▷ (KA ∘ HA)
  a₄ = comp-assoc (KA ∘ HA) LZ e
  z = a₄ ∙ (a₃ ∙ (a₂ ∙ (a₁ ∙ u)))

  abstract
    source-endpoint : Iso₂ (Pasted.source-evaluation ∙ z) u

    source-endpoint = cancel-evaluation-pairs a₁ a₂ a₃ a₄ u ∙
      isoComp-cong
        (isoComp-cong
          (isoComp-cong (pre-inverse uk HA) (idIso (invIso a₂)))
          (isoComp-cong (pre-inverse β (KA ∘ HA)) (idIso (invIso a₄))))
        (idIso z)

  composite-input = comp-assoc KHA LZ e ∙ ((β ▷ KHA) ∙ (v ∙ τ))
  input-action = e ◁ (LZ ◁ κA)

  abstract
    input-square : Iso₂
      (comp-assoc KHA LZ e ∙ ((β ▷ KHA) ∙ (U ◁ κA)))
      (input-action ∙ (a₄ ∙ a₃))

    input-square = isoComp-assoc-at input-action a₄ a₃ ∙
      (isoComp-cong (postWhisker-comp-at κA LZ e) (idIso a₃) ∙
      (invIso (isoComp-assoc-at (comp-assoc KHA LZ e) ((e ∘ LZ) ◁ κA) a₃) ∙
        isoComp-cong (idIso (comp-assoc KHA LZ e)) (interchange-at β κA)))

  abstract
    input-endpoint : Iso₂ composite-input (input-action ∙ z)

    input-endpoint =
      isoComp-cong (idIso input-action) (isoComp-assoc-at a₄ a₃ (a₂ ∙ (a₁ ∙ u))) ∙
      (isoComp-assoc-at input-action (a₄ ∙ a₃) (a₂ ∙ (a₁ ∙ u)) ∙
      (isoComp-cong input-square (idIso (a₂ ∙ (a₁ ∙ u))) ∙
      (invIso (isoComp-assoc-at (comp-assoc KHA LZ e) ((β ▷ KHA) ∙ (U ◁ κA)) (a₂ ∙ (a₁ ∙ u))) ∙
      (isoComp-cong (idIso (comp-assoc KHA LZ e))
        (invIso (isoComp-assoc-at (β ▷ KHA) (U ◁ κA) (a₂ ∙ (a₁ ∙ u)))) ∙
        isoComp-cong (idIso (comp-assoc KHA LZ e))
          (isoComp-cong (idIso (β ▷ KHA)) (funUncurry-pre-iterated (funPre f) k h))))))

  output-associator = invIso (comp-assoc LX KHB e)
  output-action = e ◁ (κB ▷ LX)
  abstract
    output-endpoint : Iso₂
      ((w ▷ LX) ∙ (output-associator ∙ output-action)) Pasted.target-evaluation

    output-endpoint = invIso normalize-target ∙
      (isoComp-cong restricted-cancellation (idIso final-associator) ∙
      (invIso (isoComp-assoc-at (w ▷ LX) ((e ◁ κB) ▷ LX) final-associator) ∙
        isoComp-cong (idIso (w ▷ LX))
          (move-square (comp-assoc LX KHB e) ((e ◁ κB) ▷ LX) output-action
            (comp-assoc LX (KB ∘ HB) e) (whisker-mixed-at κB LX e))))
      where
      final-associator : NatIso (e ∘ ((KB ∘ HB) ∘ LX)) ((e ∘ (KB ∘ HB)) ∘ LX)
      final-associator = invIso (comp-assoc LX (KB ∘ HB) e)
      before : NatIso (e ∘ (KB ∘ HB)) ((e ∘ KB) ∘ HB)
      before = invIso (comp-assoc HB KB e)
      image-cancellation : Iso₂ ((e ◁ invIso κB) ∙ (e ◁ κB)) (idIso (e ∘ (KB ∘ HB)))
      image-cancellation = postWhisker-idIso e (KB ∘ HB) ∙
        ((postWhisker e ◁ isoComp-inverseˡ-at κB) ∙
          invIso (postWhisker-isoComp-at e (invIso κB) κB))
      cancellation : Iso₂ (w ∙ (e ◁ κB)) before
      cancellation = isoComp-unitʳ-at before ∙
        (isoComp-cong (idIso before) image-cancellation ∙
          isoComp-assoc-at before (e ◁ invIso κB) (e ◁ κB))
      restricted-cancellation : Iso₂ ((w ▷ LX) ∙ ((e ◁ κB) ▷ LX)) (before ▷ LX)
      restricted-cancellation = (preWhisker LX ◁ cancellation) ∙
        invIso (preWhisker-isoComp-at w (e ◁ κB) LX)
      normalize-target : Iso₂ Pasted.target-evaluation ((before ▷ LX) ∙ final-associator)
      normalize-target = isoComp-cong
        (preWhisker LX ◁ (isoComp-unitˡ-at before ∙
          isoComp-cong (preWhisker-idIso (funUncurry k) HB) (idIso before)))
        (idIso final-associator)

```
