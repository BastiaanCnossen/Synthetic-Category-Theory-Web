# Pasting the transposed restriction squares

We reverse the product-symmetry squares and evaluate their pasting. The
inner boundary cancels against the chosen transposition comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section04.RetainedCompositionParameterChange as Project
import SCT.VolumeI.Chapter01.Section08.RestrictionMate as Mate

module SCT.VolumeI.Chapter01.Section08.TranspositionCompositionBase
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.Transposition 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.EvaluationMateCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section04.ParameterSquarePasting 𝒯 using (paste)
open import SCT.VolumeI.Chapter01.Section04.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section06.InverseCalculus 𝒯 using (pre-inverse)

module CompositorEvaluation {X A B C E : CAT}
  (f : MAP A B) (g : MAP B C) (h : MAP C (Fun X E)) where
  e = funUncurry h
  U = transpose h
  Uf = funUncurry (h ∘ g)
  HA = swap {X} {A}
  HB = swap {X} {B}
  HC = swap {X} {C}
  Xf = productRestriction X f
  Xg = productRestriction X g
  Yf = productMap f (id X)
  Yg = productMap g (id X)
  β = funUncurry-restrict h g
  qg = transpose-pre g h
  uk = idIso (transpose (h ∘ g))
  Shf = swap-restriction {X} f
  Shg = swap-restriction {X} g
  module Pasted = Project.EvaluationPaste 𝒯 M Xf Xg Yf Yg HA HB HC
    e U Uf (transpose (h ∘ g))
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

  r = transpose-pre f (h ∘ g)
  μ = funUncurry-restrict (h ∘ g) f
  tail = μ ▷ HA
  before = comp-assoc HA Yf Uf
  across = Uf ◁ Shf
  after = comp-assoc Xf HB Uf

  abstract
    core-action : (Pasted.evaluation-action ∙ r) =₂ tail
    core-action = cancel-mate before across after (Uf ◁ Shf ⁻¹) (uk ▷ Xf) r tail
      (post-inverse Uf Shf)
      (isoComp-unitˡ-at r ∙ isoComp-cong (preWhisker-idIso (transpose (h ∘ g)) Xf) (idIso r))

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
