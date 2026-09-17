# Composition of functor-category restrictions after evaluation

The restriction compositor is evaluated by pasting the two separation
squares. The parameter-change comparison supplies the inner edge, and
the mixed product composition law supplies the outer edge.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section03.RetainedCompositionParameterChange as Project
import SCT.VolumeI.Chapter01.Section08.FunPrecompositionParameterChange as Parameter
import SCT.VolumeI.Chapter01.Section08.FunPrecompositionCompositeImage as Image
import SCT.VolumeI.Chapter01.Section01.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section02.Structural as Structural

module SCT.VolumeI.Chapter01.Section08.FunPrecompositionCompositionBase
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section06.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.FunctorSquares 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section08.EvaluationMateCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section08.ProductMixedSubstitution 𝒯 M using (separate-composition)
open import SCT.VolumeI.Chapter01.Section03.ParameterSquarePasting 𝒯 using (paste)
open import SCT.VolumeI.Chapter01.Section03.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section05.InverseCalculus 𝒯 using (pre-inverse)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left; cancel-right; move-square)
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-comp-at; whisker-mixed-at)

module CompositorEvaluation {X A B C E : CAT} (f : MAP A B) (g : MAP B C) (h : MAP X (Fun C E)) where
  module Lifted = Image.CompositorImage 𝒯 M ℱ P f g h
  Y = Fun C E
  e = funEval {C = C} {D = E}
  U = funUncurry h
  Fg = funPre {D = E} g
  Ff = funPre {D = E} f
  Uf = funUncurry Fg
  HA = productMap h (id A)
  HB = productMap h (id B)
  HC = productMap h (id C)
  Xf = productRestriction X f
  Xg = productRestriction X g
  Yf = productRestriction Y f
  Yg = productRestriction Y g
  β = funPre-β {D = E} g
  qg = funPre-uncurry g h
  uk = funUncurry-pre Fg h
  Shf = productMap-separate h f
  Shg = productMap-separate h g
  module Restriction = Parameter.ParameterChange 𝒯 M ℱ g h (id X)
  module Change = Parameter.ParameterChange 𝒯 M ℱ f Fg h
  module Pasted = Project.EvaluationPaste 𝒯 M Xf Xg Yf Yg HA HB HC
    e U Uf (funUncurry (Fg ∘ h))
    (idIso U) (invIso β) (invIso qg) (invIso Shg) (invIso Shf) uk

  source-base = (invIso β ▷ HB) ∙ invIso (comp-assoc HB Yg e)
  target-base = (idIso U ▷ Xg) ∙ invIso (comp-assoc Xg HC e)
  normalized-source = invIso uk ∙ source-base

  abstract
    inverse-square : Iso₂ (normalized-source ∙ (e ◁ invIso Shg)) (invIso qg ∙ target-base)
    inverse-square = Project.projection-inverse-action 𝒯 M e normalized-source target-base Shg qg Restriction.square

    normalize-inverse-square : Iso₂ (uk ∙ (normalized-source ∙ (e ◁ invIso Shg)))
      (source-base ∙ (e ◁ invIso Shg))
    normalize-inverse-square = isoComp-cong (cancel-inverse uk source-base) (idIso (e ◁ invIso Shg)) ∙
      invIso (isoComp-assoc-at uk normalized-source (e ◁ invIso Shg))

    square : Iso₂ (source-base ∙ (e ◁ invIso Shg))
      (uk ∙ (invIso qg ∙ target-base))
    square = isoComp-cong (idIso uk) inverse-square ∙ invIso normalize-inverse-square
    pasted-evaluation : Iso₂
      (Pasted.target-evaluation ∙ (e ◁ paste (invIso Shg) (invIso Shf)))
      (Pasted.evaluation-action ∙ Pasted.source-evaluation)
    pasted-evaluation = Pasted.project-paste square

  τ = funUncurryIso (comp-assoc h Fg Ff)
  r = funPre-uncurry f (Fg ∘ h) ∙ τ
  u₀ = funUncurry-pre (Ff ∘ Fg) h
  tail = (funPre-uncurry f Fg ▷ HA) ∙ u₀
  before = comp-assoc HA Yf Uf
  across = Uf ◁ Shf
  after = comp-assoc Xf HB Uf

  abstract
    parameter-tail : Iso₂ (Change.Pasted.evaluation-action ∙ u₀)
      (invIso after ∙ (across ∙ (before ∙ tail)))
    parameter-tail = append-four (invIso after) across before (funPre-uncurry f Fg ▷ HA) u₀

    core-action : Iso₂ (Pasted.evaluation-action ∙ r) tail
    core-action = cancel-mate before across after (Uf ◁ invIso Shf) (uk ▷ Xf) r tail
      (post-inverse Uf Shf) (parameter-tail ∙ Change.comparison)

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
