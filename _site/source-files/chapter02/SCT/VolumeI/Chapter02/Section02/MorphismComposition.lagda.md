# Composition with specified endpoints

Two morphism families with a common middle object determine a composable
pair. Its matching goes through the specified middle object, using the
target frame of the first arrow and the inverse source frame of the second.
The complete pullback beta law retains this chosen matching.

The three endpoint frames place the pair over its source, middle and
target objects. Applying the existing Segal composition over the outer
vertices therefore gives a morphism family with the requested endpoints.
This is the same chosen composition, with its endpoint data made explicit.
It does not establish the unit or associativity laws.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.MorphismComposition where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (terminate; module Constructions)
open Constructions using (const; terminal-identification)
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
open Coherence using (comp-assoc)
open Coherence.Composition
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (Ar; ev₀; ev₁; MorphismFamily)
open import SCT.VolumeI.Chapter02.Section01.HomAndSlices
  using (Hom; endpointMap; module EndpointFiber)
open import SCT.VolumeI.Chapter02.Section01.Triangles
  using (Composable; Vertices; pair-vertices; pairs-over; arrows-over;
    outer-vertices; short-edges)
open import SCT.VolumeI.Chapter02.Section02.SegalComposition
  using (module ChosenComposition)

module ComposableFamilies {Γ : Context} {P C : CAT Γ}
  {f g h : MAP P C} (α : MorphismFamily f g) (β : MorphismFamily g h) where

  cone : Cone ev₁ ev₀ P
  cone = record
    { left = MorphismFamily.arrow α
    ; right = MorphismFamily.arrow β
    ; match = (MorphismFamily.source-frame β) ⁻¹ ∙ MorphismFamily.target-frame α }

  pair-map : MAP P (Composable C)
  pair-map = pullback-factor cone

  pair-image : ConeIdentification₁
    (cone-restrict pair-map (pullback-cone ev₁ ev₀)) cone
  pair-image = pullback-factor-β cone

  vertices : MAP P (Vertices C)
  vertices = pair (pair f g) h

  private
    first-frame : ((ev₀ ∘ pullback₁) ∘ pair-map) =₁ f
    first-frame = MorphismFamily.source-frame α ∙
      ((ev₀ ◁ ConeIdentification₁.left pair-image) ∙ comp-assoc pair-map pullback₁ ev₀)

    middle-frame : ((ev₁ ∘ pullback₁) ∘ pair-map) =₁ g
    middle-frame = MorphismFamily.target-frame α ∙
      ((ev₁ ◁ ConeIdentification₁.left pair-image) ∙ comp-assoc pair-map pullback₁ ev₁)

    last-frame : ((ev₁ ∘ pullback₂) ∘ pair-map) =₁ h
    last-frame = MorphismFamily.target-frame β ∙
      ((ev₁ ◁ ConeIdentification₁.right pair-image) ∙ comp-assoc pair-map pullback₂ ev₁)

  pair-over : FunctorOverBase (category-over P vertices) (pairs-over C)
  pair-over = functor-over pair-map
    (pair⁼ (pair⁼ first-frame middle-frame ∙
        pair-pre (ev₀ ∘ pullback₁) (ev₁ ∘ pullback₁) pair-map) last-frame ∙
      pair-pre (pair (ev₀ ∘ pullback₁) (ev₁ ∘ pullback₁))
        (ev₁ ∘ pullback₂) pair-map)

  outer-frame : (outer-vertices ∘ vertices) =₁ pair f h
  outer-frame = pair⁼ V.first V.third ∙
    pair-pre (pr₁ ∘ pr₁) pr₂ vertices
    where module V = Triple f g h

module Composition {Γ : Context} (C : CAT Γ)
  (segal : IsEquiv (short-edges C)) where

  private
    module Chosen = ChosenComposition C segal using (composition; composition-over)

  module Composite {P : CAT Γ} {f g h : MAP P C}
    (β : MorphismFamily g h) (α : MorphismFamily f g) where

    private
      module Input = ComposableFamilies α β

    over : FunctorOverMap outer-vertices
      (category-over P Input.vertices) (arrows-over C)
    over = comp-over-map outer-vertices Chosen.composition-over Input.pair-over

    arrow : MAP P (Ar C)
    arrow = Chosen.composition ∘ Input.pair-map

    endpoint-frame : (pair ev₀ ev₁ ∘ arrow) =₁ pair f h
    endpoint-frame = Input.outer-frame ∙ FunctorOverBase.cell over

    value : MorphismFamily f h
    value = record
      { arrow = arrow
      ; source-frame = pair-β₁ f h ∙
          ((pr₁ ◁ endpoint-frame) ∙ (project-pair₁ ev₀ ev₁ arrow) ⁻¹)
      ; target-frame = pair-β₂ f h ∙
          ((pr₂ ◁ endpoint-frame) ∙ (project-pair₂ ev₀ ev₁ arrow) ⁻¹) }

  compose : {P : CAT Γ} {f g h : MAP P C}
    → MorphismFamily g h → MorphismFamily f g → MorphismFamily f h
  compose = Composite.value
```

The Hom composition functor applies this family construction to the two
universal arrows on `Hom C y z × Hom C x y`. The terminal base legs of
the Hom pullbacks are identified with the chosen terminal map. The result
therefore determines a cone defining a functor into `Hom C x z`. Its beta
law records the full endpoint matching, as well as the resulting arrow
and the terminal base leg.

```agda
module _ {Γ : Context} {P C : CAT Γ} (x y : MAP One C) where
  hom-family : (r : MAP P (Hom C x y)) → MorphismFamily (const x) (const y)
  hom-family r = record
    { arrow = EndpointFiber.arrow x y ∘ r
    ; source-frame = (x ◁ terminal-identification base (terminate P)) ∙
        (project-pair₁ x y base ∙
          ((pr₁ ◁ matching) ∙ (project-pair₁ ev₀ ev₁ arrow) ⁻¹))
    ; target-frame = (y ◁ terminal-identification base (terminate P)) ∙
        (project-pair₂ x y base ∙
          ((pr₂ ◁ matching) ∙ (project-pair₂ ev₀ ev₁ arrow) ⁻¹)) }
    where
      cone : Cone (endpointMap C) (pair x y) P
      cone = cone-restrict r (EndpointFiber.universal x y)
      arrow : MAP P (Ar C)
      arrow = Cone.left cone
      base : MAP P One
      base = Cone.right cone
      matching : (endpointMap C ∘ arrow) =₁ (pair x y ∘ base)
      matching = Cone.match cone

module HomComposition {Γ : Context} (C : CAT Γ)
  (segal : IsEquiv (short-edges C)) (x y z : MAP One C) where

  private
    P : CAT Γ
    P = Hom C y z × Hom C x y

  first : MorphismFamily (const {P = P} x) (const y)
  first = hom-family x y pr₂

  second : MorphismFamily (const {P = P} y) (const z)
  second = hom-family y z pr₁

  composite : MorphismFamily (const {P = P} x) (const z)
  composite = Composition.compose C segal second first

  value : MAP (Hom C y z × Hom C x y) (Hom C x z)
  value = EndpointFiber.extension x z (terminate P) composite

  image : ConeIdentification₁
    (cone-restrict value (EndpointFiber.universal x z))
    (EndpointFiber.boundary-cone x z (terminate P) composite)
  image = EndpointFiber.extension-image x z (terminate P) composite
```
