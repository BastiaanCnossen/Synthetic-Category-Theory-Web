# Hom categories as fibers of slice projections

Taking the fiber of a category of framed arrows amounts to evaluating its
two endpoint functors. The comparison below includes the specified changes
of both endpoint values and uses pullback pasting before any initiality or
terminality assumption.

For a slice or coslice, this identifies the projection fiber with the stated
Hom category. If the object is terminal or initial, that projection is an
equivalence, so the Hom category is contractible. Neither the converse nor
the assertion that every Hom category is an anima is used here.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.SliceFibers where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (terminate; module Constructions)
open Constructions using (IsContractible; terminal-identification; const)
open import SCT.VolumeI.Chapter01.Section02.Coherence using (comp-unitˡ; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization using (const-evaluate)
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (id-isEquiv; equiv-transport)
open import SCT.VolumeI.Chapter01.Section06.Pullbacks using (Pullback)
import SCT.VolumeI.Chapter01.Section06.ProjectionFibers as Fibers
open import SCT.VolumeI.Chapter02.Section01.HomAndSlices
  using (Hom; module EndpointFiber; endpointMap; IsInitial; IsTerminal)

module _ {Γ : Context} where
  module EndpointFiberAt {B C : CAT Γ} (u v : MAP B C) (y : MAP One B)
    (x₀ x₁ : MAP One C) (α : (u ∘ y) =₁ x₀) (β : (v ∘ y) =₁ x₁) where

    endpoint-comparison : (pair u v ∘ y) =₁ pair x₀ x₁
    endpoint-comparison = pair⁼ α β ∙ pair-pre u v y

    private
      module Fiber = Fibers.FiberComparison (endpointMap C) (pair u v) y
        (pair x₀ x₁) endpoint-comparison

    fiber-to-hom : MAP (Pullback (EndpointFiber.base u v) y) (Hom C x₀ x₁)
    fiber-to-hom = Fiber.fiber-to-target

    fiber-to-hom-isEquiv : IsEquiv fiber-to-hom
    fiber-to-hom-isEquiv = Fiber.fiber-to-target-isEquiv

    hom-contractible : IsEquiv (EndpointFiber.base u v) → IsContractible (Hom C x₀ x₁)
    hom-contractible e = Fiber.target-contractible e
      (equiv-transport (terminal-identification (id One) (terminate One)) (id-isEquiv One))

  module TerminalFiber {C : CAT Γ} (x y : MAP One C) =
    EndpointFiberAt (id C) (const x) y y x (comp-unitˡ y) (const-evaluate x y)

  module InitialFiber {C : CAT Γ} (x y : MAP One C) =
    EndpointFiberAt (const x) (id C) y x y (const-evaluate x y) (comp-unitˡ y)

  terminal-hom-contractible : {C : CAT Γ} (x : MAP One C) → IsTerminal x
    → (y : MAP One C) → IsContractible (Hom C y x)
  terminal-hom-contractible x e y = TerminalFiber.hom-contractible x y e

  initial-hom-contractible : {C : CAT Γ} (x : MAP One C) → IsInitial x
    → (y : MAP One C) → IsContractible (Hom C x y)
  initial-hom-contractible x e y = InitialFiber.hom-contractible x y e
```
