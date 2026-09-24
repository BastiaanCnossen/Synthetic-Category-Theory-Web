# Retracts of functors

The definition retains the higher compatibility in `def:Retract`. The proof
of closure under retracts needs only the two squares and endpoint comparisons;
this does not justify deleting the compatibility from the definition.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence

module SCT.VolumeI.Chapter01.Section03.Retracts
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P) where

open Vocabulary V
open Operations V
open Coherence.CompositionStructure S
open Coherence.Composition V T P S

record RetractDiagram {C D C′ D′ : CAT} (f : MAP C D) (f′ : MAP C′ D′) : Set m where
  field
    g : MAP C C′
    h : MAP C′ C
    k : MAP D D′
    j : MAP D′ D
    leftSquare : (f′ ∘ g) =₁ (k ∘ f)
    rightSquare : (f ∘ h) =₁ (j ∘ f′)
    α : (id C) =₁ (h ∘ g)
    β : (j ∘ k) =₁ (id D)

  loop : f =₁ f
  loop = comp-unitˡ f ∙ ((β ▷ f) ∙
    ((comp-assoc f k j) ⁻¹ ∙ ((j ◁ leftSquare) ∙
    (comp-assoc g f′ j ∙ ((rightSquare ▷ g) ∙
    ((comp-assoc g h f) ⁻¹ ∙ ((f ◁ α) ∙ (comp-unitʳ f) ⁻¹)))))))

record Retract {C D C′ D′ : CAT} (f : MAP C D) (f′ : MAP C′ D′) : Set m where
  field
    diagram : RetractDiagram f f′
    compatibility : (idIso f) =₂ (RetractDiagram.loop diagram)

retract-diagram-isEquiv : {C D C′ D′ : CAT} {f : MAP C D} {f′ : MAP C′ D′}
  → RetractDiagram f f′ → IsEquiv f′ → IsEquiv f
retract-diagram-isEquiv {f = f} {f′} R e =
  let open RetractDiagram R
      u = IsEquiv.inverse e
      w = h ∘ (u ∘ k)
      counit = β ∙ ((j ◁ comp-unitˡ k) ∙
        ((j ◁ ((IsEquiv.retractionIso e) ⁻¹ ▷ k)) ∙
        ((j ◁ (comp-assoc k u f′) ⁻¹) ∙
        (comp-assoc (u ∘ k) f′ j ∙ ((rightSquare ▷ (u ∘ k)) ∙
        (comp-assoc (u ∘ k) h f) ⁻¹)))))
      inverseUnit = α ⁻¹ ∙ ((h ◁ comp-unitˡ g) ∙
        ((h ◁ ((IsEquiv.sectionIso e) ⁻¹ ▷ g)) ∙
        ((h ◁ (comp-assoc g f′ u) ⁻¹) ∙
        ((h ◁ (u ◁ leftSquare ⁻¹)) ∙
        ((h ◁ comp-assoc f k u) ∙ comp-assoc f (u ∘ k) h)))))
  in record { inverse = w ; sectionIso = inverseUnit ⁻¹ ; retractionIso = counit ⁻¹ }

retract-isEquiv : {C D C′ D′ : CAT} {f : MAP C D} {f′ : MAP C′ D′}
  → Retract f f′ → IsEquiv f′ → IsEquiv f
retract-isEquiv {f = f} {f′} R e =
  let open RetractDiagram (Retract.diagram R)
      u = IsEquiv.inverse e
      --! begin retract-inverse
      w = h ∘ (u ∘ k)
      --! end retract-inverse
      --! begin retract-counit
      counit = β ∙ ((j ◁ comp-unitˡ k) ∙
        ((j ◁ ((IsEquiv.retractionIso e) ⁻¹ ▷ k)) ∙
        ((j ◁ (comp-assoc k u f′) ⁻¹) ∙
        (comp-assoc (u ∘ k) f′ j ∙ ((rightSquare ▷ (u ∘ k)) ∙
        (comp-assoc (u ∘ k) h f) ⁻¹)))))
      --! end retract-counit
      --! begin retract-inverse-unit
      inverseUnit = α ⁻¹ ∙ ((h ◁ comp-unitˡ g) ∙
        ((h ◁ ((IsEquiv.sectionIso e) ⁻¹ ▷ g)) ∙
        ((h ◁ (comp-assoc g f′ u) ⁻¹) ∙
        ((h ◁ (u ◁ leftSquare ⁻¹)) ∙
        ((h ◁ comp-assoc f k u) ∙ comp-assoc f (u ∘ k) h)))))
      --! end retract-inverse-unit
  in record { inverse = w ; sectionIso = inverseUnit ⁻¹ ; retractionIso = counit ⁻¹ }

```
