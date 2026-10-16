# Hom categories and slices

The endpoint map sends an arrow to its source and target. Pulling it back
along a pair of functors gives their category of arrows with specified
endpoints. The chosen pullback retains both the arrow and the base functor,
together with the complete endpoint matching.

A framed family over a specified base functor supplies a cone and hence an
extension into this category. The pullback beta law identifies the entire
induced cone with the supplied cone.
For identifications over varying bases, recovery uses both cone legs and
their matching square, with an independent identification parameter X.

Hom, slice and coslice categories specialize this one construction.
Initial and terminal objects are defined by equivalence of the respective
projection. The Hom construction retains its terminal base leg; eliminating
that leg requires terminality and is not a definitional simplification.

The final two declarations migrate the existing manuscript axiom that zero
is initial and one is terminal in the directed interval.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.HomAndSlices where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence using (module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares using (module PullbackRecovery)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using (zero; one)

module _ {Γ : Context} where
  endpointMap : (C : CAT Γ) → MAP (Ar C) (C × C)
  endpointMap C = pair ev₀ ev₁

  module EndpointFiber {P C : CAT Γ} (f g : MAP P C) where
    category : CAT Γ
    category = Pullback (endpointMap C) (pair f g)

    universal : Cone (endpointMap C) (pair f g) category
    universal = pullback-cone (endpointMap C) (pair f g)

    arrow : MAP category (Ar C)
    arrow = Cone.left universal
    base : MAP category P
    base = Cone.right universal
    matching : (endpointMap C ∘ arrow) =₁ (pair f g ∘ base)
    matching = Cone.match universal

    boundary-cone : {T : CAT Γ} (r : MAP T P)
      → MorphismFamily (f ∘ r) (g ∘ r) → Cone (endpointMap C) (pair f g) T
    boundary-cone r α = record
      { left = MorphismFamily.arrow α
      ; right = r
      ; match = (pair-pre f g r) ⁻¹ ∙
          (pair⁼ (MorphismFamily.source-frame α) (MorphismFamily.target-frame α) ∙
            pair-pre ev₀ ev₁ (MorphismFamily.arrow α)) }

    extension : {T : CAT Γ} (r : MAP T P)
      → MorphismFamily (f ∘ r) (g ∘ r) → MAP T category
    extension r α = pullback-factor (boundary-cone r α)

    extension-image : {T : CAT Γ} (r : MAP T P) (α : MorphismFamily (f ∘ r) (g ∘ r))
      → ConeIdentification₁ (cone-restrict (extension r α) universal) (boundary-cone r α)
    extension-image r α = pullback-factor-β (boundary-cone r α)

    extension-arrow : {T : CAT Γ} (r : MAP T P) (α : MorphismFamily (f ∘ r) (g ∘ r))
      → (arrow ∘ extension r α) =₁ MorphismFamily.arrow α
    extension-arrow r α = ConeIdentification₁.left (extension-image r α)

    extension-base : {T : CAT Γ} (r : MAP T P) (α : MorphismFamily (f ∘ r) (g ∘ r))
      → (base ∘ extension r α) =₁ r
    extension-base r α = ConeIdentification₁.right (extension-image r α)

    module Identifications {T X : CAT Γ} (h k : MAP T category)
      (Φ : ConeIdentification X (cone-restrict h universal) (cone-restrict k universal)) where
      module Recovery = PullbackRecovery h k Φ
        using (identification; recovery-law; left-image; right-image; matching-image)
      open Recovery public

  Hom : (C : CAT Γ) → MAP One C → MAP One C → CAT Γ
  Hom C x y = EndpointFiber.category x y

  Slice Coslice : (C : CAT Γ) → MAP One C → CAT Γ
  Slice C x = EndpointFiber.category (id C) (const x)
  Coslice C x = EndpointFiber.category (const x) (id C)

  slice-projection : {C : CAT Γ} (x : MAP One C) → MAP (Slice C x) C
  slice-projection {C} x = EndpointFiber.base (id C) (const x)
  coslice-projection : {C : CAT Γ} (x : MAP One C) → MAP (Coslice C x) C
  coslice-projection {C} x = EndpointFiber.base (const x) (id C)

  IsTerminal IsInitial : {C : CAT Γ} → MAP One C → Set m
  IsTerminal x = IsEquiv (slice-projection x)
  IsInitial x = IsEquiv (coslice-projection x)

  -- Initial and terminal endpoints of the directed interval.
  postulate
    interval-zero-initial : IsInitial (zero {Γ = Γ})
    interval-one-terminal : IsTerminal (one {Γ = Γ})
```
