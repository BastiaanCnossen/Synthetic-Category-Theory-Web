# Pasting the decodeMapd restriction squares

We reverse the terminal-product squares and evaluate their pasting. The
inner boundary cancels against the chosen decoding comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping

import SCT.VolumeI.Chapter01.Section04.RetainedCompositionParameterChange as Project
import SCT.VolumeI.Chapter01.Section08.RestrictionMate as Mate

module SCT.VolumeI.Chapter01.Section08.DecodingCompositionBase
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.DecodingNaturality 𝒯 M using (decodePre; oneProduct-natural)
open import SCT.VolumeI.Chapter01.Section08.EvaluationMateCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section04.ParameterSquarePasting 𝒯 using (paste)
open import SCT.VolumeI.Chapter01.Section04.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section06.InverseCalculus 𝒯 using (pre-inverse)

module CompositorEvaluation {A B C E : CAT}
  (f : MAP A B) (g : MAP B C) (h : Obj-abs (Map C E)) where
  e = mapUncurry h
  U = decodeMap h
  Uf = mapUncurry (mapPre g ∘ h)
  HA = oneProduct-in A
  HB = oneProduct-in B
  HC = oneProduct-in C
  Xf = f
  Xg = g
  Yf = productRestriction One f
  Yg = productRestriction One g
  β = mapPre-uncurry g h
  qg = decodePre g h
  uk = idIso (decodeMap (mapPre g ∘ h))
  Shf = oneProduct-natural f
  Shg = oneProduct-natural g
  module Pasted = Project.EvaluationPaste 𝒯 M Xf Xg Yf Yg HA HB HC
    e U Uf (decodeMap (mapPre g ∘ h))
    (idIso U) (β ⁻¹) (qg ⁻¹) (Shg ⁻¹) (Shf ⁻¹) uk
  module Boundary = Mate.Boundary 𝒯
    (comp-assoc HB Yg e) (β ▷ HB) (comp-assoc Xg HC e)
    (e ◁ Shg) (β ⁻¹ ▷ HB) (e ◁ Shg ⁻¹) (idIso U ▷ Xg)
    (pre-inverse β HB) (post-inverse e Shg) (preWhisker-idIso U Xg)

  abstract
    square :
      (Boundary.source ∙ (e ◁ Shg ⁻¹)) =₂
      (uk ∙ (qg ⁻¹ ∙ Boundary.target))
    square = (isoComp-unitˡ-at (qg ⁻¹ ∙ Boundary.target)) ⁻¹ ∙ Boundary.inverse-square

    pasted-evaluation :
      (Pasted.target-evaluation ∙ (e ◁ paste (Shg ⁻¹) (Shf ⁻¹))) =₂
      (Pasted.evaluation-action ∙ Pasted.source-evaluation)
    pasted-evaluation = Pasted.project-paste square

  raw-restriction = decodePre f (mapPre g ∘ h)
  τ = decodeMapIso (comp-assoc h (mapPre g) (mapPre f))
  u₀ = τ
  r = raw-restriction ∙ τ
  μ = mapPre-uncurry f (mapPre g ∘ h)
  tail = (μ ▷ HA) ∙ τ
  before = comp-assoc HA Yf Uf
  across = Uf ◁ Shf
  after = comp-assoc Xf HB Uf

  abstract
    raw-core-action : (Pasted.evaluation-action ∙ raw-restriction) =₂ (μ ▷ HA)
    raw-core-action = cancel-mate before across after (Uf ◁ Shf ⁻¹) (uk ▷ Xf)
      raw-restriction (μ ▷ HA) (post-inverse Uf Shf)
      (isoComp-unitˡ-at raw-restriction ∙
        isoComp-cong (preWhisker-idIso (decodeMap (mapPre g ∘ h)) Xf) (idIso raw-restriction))

    core-action : (Pasted.evaluation-action ∙ r) =₂ tail
    core-action = isoComp-cong raw-core-action (idIso τ) ∙
      (isoComp-assoc-at Pasted.evaluation-action raw-restriction τ) ⁻¹
  a₁ = qg ▷ Xf
  a₂ = comp-assoc Xf Xg U
  a₃ = comp-assoc (Xg ∘ Xf) HC e
  z = a₃ ∙ (a₂ ∙ (a₁ ∙ r))

  abstract
    source-endpoint : (Pasted.source-evaluation ∙ z) =₂ r
    source-endpoint = cancel-three-images a₁ a₂ a₃ r (qg ⁻¹ ▷ Xf)
      (idIso U ▷ (Xg ∘ Xf)) (pre-inverse qg Xf) (preWhisker-idIso U (Xg ∘ Xf))

    core-transfer :
      ((Pasted.target-evaluation ∙ (e ◁ paste (Shg ⁻¹) (Shf ⁻¹))) ∙ z) =₂ tail
    core-transfer = close-paste Pasted.target-evaluation
      (e ◁ paste (Shg ⁻¹) (Shf ⁻¹)) z Pasted.evaluation-action
      Pasted.source-evaluation r tail pasted-evaluation source-endpoint core-action
```
