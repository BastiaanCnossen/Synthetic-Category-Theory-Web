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
import SCT.VolumeI.Chapter01.Section01.Coherence as Coherence

module SCT.VolumeI.Chapter01.Section02.Retracts
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
    leftSquare : =₁ (f′ ∘ g) (k ∘ f)
    rightSquare : =₁ (f ∘ h) (j ∘ f′)
    α : =₁ (id C) (h ∘ g)
    β : =₁ (j ∘ k) (id D)

  loop : =₁ f f
  loop = comp-unitˡ f ∙ ((β ▷ f) ∙
    (invIso (comp-assoc f k j) ∙ ((j ◁ leftSquare) ∙
    (comp-assoc g f′ j ∙ ((rightSquare ▷ g) ∙
    (invIso (comp-assoc g h f) ∙ ((f ◁ α) ∙ invIso (comp-unitʳ f))))))))

record Retract {C D C′ D′ : CAT} (f : MAP C D) (f′ : MAP C′ D′) : Set m where
  field
    diagram : RetractDiagram f f′
    compatibility : =₂ (idIso f) (RetractDiagram.loop diagram)

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
        ((j ◁ (invIso (IsEquiv.retractionIso e) ▷ k)) ∙
        ((j ◁ invIso (comp-assoc k u f′)) ∙
        (comp-assoc (u ∘ k) f′ j ∙ ((rightSquare ▷ (u ∘ k)) ∙
        invIso (comp-assoc (u ∘ k) h f))))))
      --! end retract-counit
      --! begin retract-inverse-unit
      inverseUnit = invIso α ∙ ((h ◁ comp-unitˡ g) ∙
        ((h ◁ (invIso (IsEquiv.sectionIso e) ▷ g)) ∙
        ((h ◁ invIso (comp-assoc g f′ u)) ∙
        ((h ◁ (u ◁ invIso leftSquare)) ∙
        ((h ◁ comp-assoc f k u) ∙ comp-assoc f (u ∘ k) h)))))
      --! end retract-inverse-unit
  in record { inverse = w ; sectionIso = invIso inverseUnit ; retractionIso = invIso counit }
```
