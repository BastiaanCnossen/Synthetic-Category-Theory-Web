# Pasting the transposed restriction squares

We reverse the product-symmetry squares and evaluate their pasting. The
inner boundary cancels against the chosen transposition comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section03.RetainedCompositionParameterChange as Project
import SCT.VolumeI.Chapter01.Section08.RestrictionMate as Mate

module SCT.VolumeI.Chapter01.Section08.TranspositionCompositionBase
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section06.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.Transposition 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.EvaluationMateCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section03.ParameterSquarePasting 𝒯 using (paste)
open import SCT.VolumeI.Chapter01.Section03.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section05.InverseCalculus 𝒯 using (pre-inverse)

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
  β = funUncurry-pre h g
  qg = transpose-pre g h
  uk = idIso (transpose (h ∘ g))
  Shf = swap-restriction {X} f
  Shg = swap-restriction {X} g
  module Pasted = Project.EvaluationPaste 𝒯 M Xf Xg Yf Yg HA HB HC
    e U Uf (transpose (h ∘ g))
    (idIso U) (invIso β) (invIso qg) (invIso Shg) (invIso Shf) uk
  module Boundary = Mate.Boundary 𝒯
    (comp-assoc HB Yg e) (β ▷ HB) (comp-assoc Xg HC e)
    (e ◁ Shg) (invIso β ▷ HB) (e ◁ invIso Shg) (idIso U ▷ Xg)
    (pre-inverse β HB) (post-inverse e Shg) (preWhisker-idIso U Xg)

  abstract
    square : Iso₂
      (Boundary.source ∙ (e ◁ invIso Shg))
      (uk ∙ (invIso qg ∙ Boundary.target))
    square = invIso (isoComp-unitˡ-at (invIso qg ∙ Boundary.target)) ∙ Boundary.inverse-square

    pasted-evaluation : Iso₂
      (Pasted.target-evaluation ∙ (e ◁ paste (invIso Shg) (invIso Shf)))
      (Pasted.evaluation-action ∙ Pasted.source-evaluation)
    pasted-evaluation = Pasted.project-paste square

  r = transpose-pre f (h ∘ g)
  μ = funUncurry-pre (h ∘ g) f
  tail = μ ▷ HA
  before = comp-assoc HA Yf Uf
  across = Uf ◁ Shf
  after = comp-assoc Xf HB Uf

  abstract
    core-action : Iso₂ (Pasted.evaluation-action ∙ r) tail
    core-action = cancel-mate before across after (Uf ◁ invIso Shf) (uk ▷ Xf) r tail
      (post-inverse Uf Shf)
      (isoComp-unitˡ-at r ∙ isoComp-cong (preWhisker-idIso (transpose (h ∘ g)) Xf) (idIso r))

  a₁ = qg ▷ Xf
  a₂ = comp-assoc Xf Xg U
  a₃ = comp-assoc (Xg ∘ Xf) HC e
  z = a₃ ∙ (a₂ ∙ (a₁ ∙ r))

  abstract
    source-endpoint : Iso₂ (Pasted.source-evaluation ∙ z) r
    source-endpoint = cancel-three-images a₁ a₂ a₃ r (invIso qg ▷ Xf)
      (idIso U ▷ (Xg ∘ Xf)) (pre-inverse qg Xf) (preWhisker-idIso U (Xg ∘ Xf))

    core-transfer : Iso₂
      ((Pasted.target-evaluation ∙ (e ◁ paste (invIso Shg) (invIso Shf))) ∙ z) tail
    core-transfer = close-paste Pasted.target-evaluation
      (e ◁ paste (invIso Shg) (invIso Shf)) z Pasted.evaluation-action
      Pasted.source-evaluation r tail pasted-evaluation source-endpoint core-action
```
