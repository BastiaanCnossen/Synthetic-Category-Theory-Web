# The base projection of retained composition change

We compare the first projections of the two retained composition routes.
Both carry the same specified witness to the base. Cancellation of that
witness gives the required identification of projections.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Currying as Currying
import SCT.VolumeI.Chapter01.Section04.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section04.InternalCoherence as Internal
import SCT.VolumeI.Chapter01.Section04.RetainedComparisonLaws as Retained
import SCT.VolumeI.Chapter01.Section04.ParameterChange as Change
import SCT.VolumeI.Chapter01.Section04.RetainedParameterChangeProjections as ChangeProjections
import SCT.VolumeI.Chapter01.Section04.RetainedCompositionRoutes as CompositionRoutes
import SCT.VolumeI.Chapter01.Section04.ProjectionSquares as ProjectionSquares
import SCT.VolumeI.Chapter01.Section04.ParameterSquarePasting as ParameterSquarePasting
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PairingNaturality

module SCT.VolumeI.Chapter01.Section04.RetainedCompositionBaseChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open Currying 𝒯 M
open MapComposition 𝒯 M using (composeTerm)
open Change 𝒯 M using (retained-parameter-change)
open ProjectionSquares 𝒯
open ParameterSquarePasting 𝒯 using (paste)
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-left-reflect)
module R = Internal.RetainedEvaluation 𝒯 M
module S = Retained.RetainedSquares 𝒯 M

module BaseChange {P Q : CAT} (σ : MAP Q P) where
  projection : (C : CAT) → MAP (Q × C) P
  projection C = σ ∘ pr₁

  substitution : (C : CAT) → MAP (Q × C) (P × C)
  substitution C = productMap σ (id C)

  substitution-base : (C : CAT) → (pr₁ ∘ substitution C) =₁ (projection C)
  substitution-base C = pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂)

  term-base : {C D : CAT} (f : MAP Q (Map C D))
    → (projection D ∘ R.retained Q f) =₁ (projection C)
  term-base f = lift-base σ pr₁ (R.retained Q f) (S.retained-base Q f)

  abstract
    change-square : {C D : CAT} (f : MAP P (Map C D))
      → Square pr₁
          (compose-base pr₁ (substitution D) (substitution-base D)
            (R.retained Q (f ∘ σ)) (term-base (f ∘ σ)))
          (compose-base pr₁ (R.retained P f) (S.retained-base P f)
            (substitution C) (substitution-base C))
          (retained-parameter-change f σ)
    change-square {D = D} f =
      let module T = ChangeProjections.ProjectionRoutes 𝒯 M f σ
      in (isoComp-assoc-at (σ ◁ T.βQ₁)
        (comp-assoc T.RQ pr₁ σ) T.t₁) ⁻¹ ∙ T.retained-change-base

    iso-square : {C D : CAT} {f g : MAP Q (Map C D)} (α : f =₁ g)
      → Square (projection D) (term-base f) (term-base g) (R.retainedIso Q α)
    iso-square {f = f} {g} α = lift-square σ pr₁
      (S.retained-base Q f) (S.retained-base Q g) (R.retainedIso Q α)
      (R.retainedIso-base Q α)

    composition-square : {C D E : CAT}
      (g : MAP Q (Map D E)) (f : MAP Q (Map C D))
      → Square (projection E) (term-base (composeTerm g f))
          (compose-base (projection E) (R.retained Q g) (term-base g)
            (R.retained Q f) (term-base f))
          (R.retained-compose Q g f)
    composition-square g f =
      lift-square σ pr₁ (S.retained-base Q (composeTerm g f))
        (compose-base pr₁ (R.retained Q g) (S.retained-base Q g)
          (R.retained Q f) (S.retained-base Q f))
        (R.retained-compose Q g f) (S.retained-compose-square Q g f) ∙
      isoComp-cong
        (lift-compose σ pr₁ (R.retained Q g) (R.retained Q f)
          (S.retained-base Q g) (S.retained-base Q f))
        (idIso (projection _ ◁ R.retained-compose Q g f))

module Calculation {P Q C D E : CAT}
  (g : MAP P (Map D E)) (f : MAP P (Map C D)) (σ : MAP Q P) where
  open CompositionRoutes.Routes 𝒯 M g f σ
  open BaseChange σ

  fQ = R.retained Q (f ∘ σ)
  gQ = R.retained Q (g ∘ σ)
  fP = R.retained P f
  gP = R.retained P g
  bf = term-base (f ∘ σ)
  bg = term-base (g ∘ σ)
  bF = S.retained-base P f
  bG = S.retained-base P g
  bx₀ = substitution-base C
  bx₁ = substitution-base D
  bx₂ = substitution-base E

  module Paste = Pasting (projection C) (projection D) (projection E)
    (pr₁ {P} {C}) (pr₁ {P} {D}) (pr₁ {P} {E})
    σC σD σE fQ gQ fP gP bf bg bF bG bx₀ bx₁ bx₂ κf κg

  source-base : (pr₁ ∘ source) =₁ (projection C)
  source-base = compose-base pr₁ σE bx₂
    (RQ.retained (composeTerm (g ∘ σ) (f ∘ σ)))
    (term-base (composeTerm (g ∘ σ) (f ∘ σ)))

  intermediate-input-base = compose-base pr₁ σE bx₂
    (RQ.retained (composeTerm g f ∘ σ)) (term-base (composeTerm g f ∘ σ))

  intermediate-output-base = compose-base pr₁ (RP.retained (composeTerm g f))
    (S.retained-base P (composeTerm g f)) σC bx₀

  abstract
    input-square : Square pr₁ source-base Paste.b₅ change-input
    input-square = compose-square pr₁ source-base Paste.b₀ Paste.b₅
      (paste κg κf) (σE ◁ RQ.retained-compose (g ∘ σ) (f ∘ σ))
      (Paste.paste-square (change-square f) (change-square g))
      (post-square pr₁ σE bx₂ (term-base (composeTerm (g ∘ σ) (f ∘ σ)))
        (compose-base (projection E) gQ bg fQ bf)
        (RQ.retained-compose (g ∘ σ) (f ∘ σ))
        (composition-square (g ∘ σ) (f ∘ σ)))

    output-square : Square pr₁ source-base Paste.b₅ restrict-output
    output-square =
      let first = inverse-square pr₁ intermediate-input-base source-base
            (σE ◁ RQ.retainedIso δ)
            (post-square pr₁ σE bx₂ (term-base (composeTerm g f ∘ σ))
              (term-base (composeTerm (g ∘ σ) (f ∘ σ)))
              (RQ.retainedIso δ) (iso-square δ))
          last = pre-square pr₁ σC (S.retained-base P (composeTerm g f))
            (compose-base pr₁ gP bG fP bF) bx₀
            (RP.retained-compose g f) (S.retained-compose-square P g f)
      in compose-square pr₁ source-base intermediate-output-base Paste.b₅
        (RP.retained-compose g f ▷ σC) (κcomp ∙ (σE ◁ RQ.retainedIso δ) ⁻¹) last
        (compose-square pr₁ source-base intermediate-input-base intermediate-output-base
          κcomp ((σE ◁ RQ.retainedIso δ) ⁻¹) (change-square (composeTerm g f)) first)

    comparison : (pr₁ ◁ change-input) =₂ (pr₁ ◁ restrict-output)
    comparison = cancel-left-reflect Paste.b₅ (output-square ⁻¹ ∙ input-square)
```
