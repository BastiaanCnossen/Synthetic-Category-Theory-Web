# Evaluating a pasted square

For an arbitrary functor `e`, evaluate a square by postcomposing its
commutativity identification and retaining the two associators. Pasting
then commutes with evaluation, with the external associators displayed.
The result is independent of functor categories and of chosen products.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.RetainedCompositionParameterChange as Project
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as Iterated
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section04.SquareCalculus.SquareEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ParameterSquarePasting 𝒯 using (paste)
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity 𝒯 M using (cancel-inverse-tail)
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (transport-pre)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right; move-square; cancel-left)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
open Structural vocabulary terminal products productLaws composition whiskering using (whisker-mixed-at; preWhisker-comp-at; postWhisker-comp-at)
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (pre-inverse-at; solve-pentagon; pentagon-whiskered)

evaluate-square : {A₀ A₁ B₀ B₁ C : CAT} (e : MAP B₁ C)
  (f : MAP A₀ A₁) (F : MAP B₀ B₁) (x₀ : MAP A₀ B₀) (x₁ : MAP A₁ B₁)
  → (x₁ ∘ f) =₁ (F ∘ x₀) → ((e ∘ x₁) ∘ f) =₁ ((e ∘ F) ∘ x₀)
evaluate-square e f F x₀ x₁ α = (comp-assoc x₀ F e) ⁻¹ ∙
  ((e ◁ α) ∙ comp-assoc f x₁ e)

abstract
  transport-identity : {X Y Z C : CAT} (e : MAP Z C) (p : MAP Y Z) (r : MAP X Y) →
    (transport-pre e p (idIso (e ∘ p)) r) =₂ ((comp-assoc r p e) ⁻¹)
  transport-identity e p r = isoComp-unitˡ-at _ ∙
    isoComp-cong (preWhisker-idIso (e ∘ p) r) (idIso _)

abstract
  evaluate-square-cong : {A₀ A₁ B₀ B₁ C : CAT} (e : MAP B₁ C)
    (f : MAP A₀ A₁) (F : MAP B₀ B₁) (x₀ : MAP A₀ B₀) (x₁ : MAP A₁ B₁)
    {α β : (x₁ ∘ f) =₁ (F ∘ x₀)} → α =₂ β →
    (evaluate-square e f F x₀ x₁ α) =₂ (evaluate-square e f F x₀ x₁ β)
  evaluate-square-cong e f F x₀ x₁ p = isoComp-cong (idIso _) (isoComp-cong (postWhisker e ◁ p) (idIso _))

  change-bottom : {A₀ A₁ B₀ B₁ C : CAT} (e : MAP B₁ C)
    (f : MAP A₀ A₁) {F F′ : MAP B₀ B₁} (x₀ : MAP A₀ B₀) (x₁ : MAP A₁ B₁)
    (δ : F =₁ F′) (α : (x₁ ∘ f) =₁ (F ∘ x₀)) →
    (evaluate-square e f F′ x₀ x₁ ((δ ▷ x₀) ∙ α)) =₂
      (((e ◁ δ) ▷ x₀) ∙ evaluate-square e f F x₀ x₁ α)
  change-bottom e f {F} {F′} x₀ x₁ δ α =
    let A = comp-assoc x₀ F e
        A′ = comp-assoc x₀ F′ e
        B = comp-assoc f x₁ e
        image = e ◁ (δ ▷ x₀)
        whiskered = (e ◁ δ) ▷ x₀
    in isoComp-assoc-at whiskered (A ⁻¹) ((e ◁ α) ∙ B) ∙
      (isoComp-cong (move-square A′ whiskered image A (whisker-mixed-at δ x₀ e)) (idIso ((e ◁ α) ∙ B)) ∙
      ((isoComp-assoc-at (A′ ⁻¹) image ((e ◁ α) ∙ B)) ⁻¹ ∙
      (isoComp-cong (idIso (A′ ⁻¹)) (isoComp-assoc-at image (e ◁ α) B) ∙
        isoComp-cong (idIso (A′ ⁻¹))
          (isoComp-cong (postWhisker-isoComp-at e (δ ▷ x₀) α) (idIso B)))))

  change-bottom-inverse : {A₀ A₁ B₀ B₁ C : CAT} (e : MAP B₁ C)
    (f : MAP A₀ A₁) {F F′ : MAP B₀ B₁} (x₀ : MAP A₀ B₀) (x₁ : MAP A₁ B₁)
    (δ : F =₁ F′) (α : (x₁ ∘ f) =₁ (F ∘ x₀)) →
    (((e ◁ δ ⁻¹) ▷ x₀) ∙ evaluate-square e f F′ x₀ x₁ ((δ ▷ x₀) ∙ α)) =₂
      (evaluate-square e f F x₀ x₁ α)
  change-bottom-inverse e f x₀ x₁ δ α =
    cancel-left ((e ◁ δ) ▷ x₀) (evaluate-square e f _ x₀ x₁ α) ∙
      isoComp-cong
        (pre-inverse-at (e ◁ δ) x₀ ∙ (preWhisker x₀ ◁ post-inverse e δ))
        (change-bottom e f x₀ x₁ δ α)

  change-evaluation : {A₀ A₁ B₀ B₁ C : CAT} {e e′ : MAP B₁ C}
    (δ : e =₁ e′) (f : MAP A₀ A₁) (F : MAP B₀ B₁)
    (x₀ : MAP A₀ B₀) (x₁ : MAP A₁ B₁) (α : (x₁ ∘ f) =₁ (F ∘ x₀)) →
    (evaluate-square e′ f F x₀ x₁ α ∙ ((δ ▷ x₁) ▷ f)) =₂
      (((δ ▷ F) ▷ x₀) ∙ evaluate-square e f F x₀ x₁ α)
  change-evaluation {e = e} {e′} δ f F x₀ x₁ α =
    paste-squares ((e ◁ α) ∙ comp-assoc f x₁ e) ((e′ ◁ α) ∙ comp-assoc f x₁ e′)
      ((comp-assoc x₀ F e) ⁻¹) ((comp-assoc x₀ F e′) ⁻¹)
      ((δ ▷ x₁) ▷ f) (δ ▷ (F ∘ x₀)) ((δ ▷ F) ▷ x₀)
      (paste-squares (comp-assoc f x₁ e) (comp-assoc f x₁ e′) (e ◁ α) (e′ ◁ α)
        ((δ ▷ x₁) ▷ f) (δ ▷ (x₁ ∘ f)) (δ ▷ (F ∘ x₀))
        (preWhisker-comp-at δ x₁ f) ((interchange-at δ α) ⁻¹))
      (move-square (comp-assoc x₀ F e′) ((δ ▷ F) ▷ x₀) (δ ▷ (F ∘ x₀))
        (comp-assoc x₀ F e) (preWhisker-comp-at δ F x₀))

  change-sides : {A₀ A₁ B₀ B₁ C : CAT} (e : MAP B₁ C)
    (f : MAP A₀ A₁) (F : MAP B₀ B₁)
    {x₀ x₀′ : MAP A₀ B₀} {x₁ x₁′ : MAP A₁ B₁}
    (δ₀ : x₀ =₁ x₀′) (δ₁ : x₁ =₁ x₁′)
    (α : (x₁ ∘ f) =₁ (F ∘ x₀)) (α′ : (x₁′ ∘ f) =₁ (F ∘ x₀′)) →
    (α′ ∙ (δ₁ ▷ f)) =₂ ((F ◁ δ₀) ∙ α) →
    (evaluate-square e f F x₀′ x₁′ α′ ∙ ((e ◁ δ₁) ▷ f)) =₂
      (((e ∘ F) ◁ δ₀) ∙ evaluate-square e f F x₀ x₁ α)
  change-sides e f F {x₀} {x₀′} {x₁} {x₁′} δ₀ δ₁ α α′ square =
    paste-squares ((e ◁ α) ∙ comp-assoc f x₁ e) ((e ◁ α′) ∙ comp-assoc f x₁′ e)
      ((comp-assoc x₀ F e) ⁻¹) ((comp-assoc x₀′ F e) ⁻¹)
      ((e ◁ δ₁) ▷ f) (e ◁ (F ◁ δ₀)) ((e ∘ F) ◁ δ₀)
      (paste-squares (comp-assoc f x₁ e) (comp-assoc f x₁′ e) (e ◁ α) (e ◁ α′)
        ((e ◁ δ₁) ▷ f) (e ◁ (δ₁ ▷ f)) (e ◁ (F ◁ δ₀))
        (whisker-mixed-at δ₁ f e)
        (postWhisker-isoComp-at e (F ◁ δ₀) α ∙
          ((postWhisker e ◁ square) ∙ (postWhisker-isoComp-at e α′ (δ₁ ▷ f)) ⁻¹)))
      (move-square (comp-assoc x₀′ F e) ((e ∘ F) ◁ δ₀) (e ◁ (F ◁ δ₀))
        (comp-assoc x₀ F e) (postWhisker-comp-at δ₀ F e))

  associate-bottom : {A₀ A₁ B₀ B₁ B₂ C : CAT}
    (e : MAP B₂ C) (f : MAP A₀ A₁) (F : MAP B₀ B₁) (G : MAP B₁ B₂)
    (x₀ : MAP A₀ B₀) (x₁ : MAP A₁ B₂)
    (α : (x₁ ∘ f) =₁ ((G ∘ F) ∘ x₀)) →
    (evaluate-square e f G (F ∘ x₀) x₁ (comp-assoc x₀ F G ∙ α)) =₂
      (comp-assoc x₀ F (e ∘ G) ∙
        ((comp-assoc F G e ⁻¹ ▷ x₀) ∙ evaluate-square e f (G ∘ F) x₀ x₁ α))
  associate-bottom e f F G x₀ x₁ α =
    let A = comp-assoc (F ∘ x₀) G e
        B = comp-assoc x₀ F (e ∘ G)
        C′ = e ◁ comp-assoc x₀ F G
        D = comp-assoc x₀ (G ∘ F) e
        E = comp-assoc F G e ▷ x₀
        tail = (e ◁ α) ∙ comp-assoc f x₁ e
        corner = (solve-pentagon A B C′ D E (pentagon-whiskered x₀ F G e)) ⁻¹
    in isoComp-cong (idIso B)
        (isoComp-cong ((pre-inverse-at (comp-assoc F G e) x₀) ⁻¹)
          (idIso ((D ⁻¹) ∙ tail)) ∙ isoComp-assoc-at (E ⁻¹) (D ⁻¹) tail) ∙
      (isoComp-assoc-at B ((E ⁻¹) ∙ D ⁻¹) tail ∙
      (isoComp-cong corner (idIso tail) ∙
      ((isoComp-assoc-at (A ⁻¹) C′ tail) ⁻¹ ∙
      (isoComp-cong (idIso (A ⁻¹)) (isoComp-assoc-at C′ (e ◁ α) (comp-assoc f x₁ e)) ∙
        isoComp-cong (idIso (A ⁻¹))
          (isoComp-cong (postWhisker-isoComp-at e (comp-assoc x₀ F G) α) (idIso (comp-assoc f x₁ e)))))))

module Pasting {A₀ A₁ A₂ B₀ B₁ B₂ C : CAT}
  (e : MAP B₂ C) (f : MAP A₀ A₁) (g : MAP A₁ A₂)
  (F : MAP B₀ B₁) (G : MAP B₁ B₂)
  (x₀ : MAP A₀ B₀) (x₁ : MAP A₁ B₁) (x₂ : MAP A₂ B₂)
  (α : (x₁ ∘ f) =₁ (F ∘ x₀)) (β : (x₂ ∘ g) =₁ (G ∘ x₁)) where

  inner = evaluate-square e g G x₁ x₂ β
  outer = evaluate-square (e ∘ G) f F x₀ x₁ α
  together = evaluate-square e (g ∘ f) (G ∘ F) x₀ x₂ (paste β α)
  action = outer ∙ (inner ▷ f)
  source-associator = comp-assoc f g (e ∘ x₂)
  input-associator = comp-assoc (g ∘ f) x₂ e
  output-associator = comp-assoc x₀ (G ∘ F) e
  target-associator = comp-assoc F G e
  module Evaluated = Project.EvaluationPaste 𝒯 M f g F G x₀ x₁ x₂
    e (e ∘ x₂) (e ∘ G) ((e ∘ x₂) ∘ g)
    (idIso _) (idIso _) (idIso _) β α inner

  abstract
    first-square :
      (transport-pre e G (idIso (e ∘ G)) x₁ ∙ (e ◁ β)) =₂
      (inner ∙ (idIso _ ∙ transport-pre e x₂ (idIso (e ∘ x₂)) g))
    first-square = right-normal ⁻¹ ∙ left-normal
      where
      left-normal : (transport-pre e G (idIso (e ∘ G)) x₁ ∙ (e ◁ β)) =₂
        ((comp-assoc x₁ G e) ⁻¹ ∙ (e ◁ β))
      left-normal = isoComp-cong (transport-identity e G x₁) (idIso (e ◁ β))
      right-normal : (inner ∙ (idIso _ ∙ transport-pre e x₂ (idIso (e ∘ x₂)) g)) =₂
        ((comp-assoc x₁ G e) ⁻¹ ∙ (e ◁ β))
      right-normal = cancel-right (comp-assoc g x₂ e) ((comp-assoc x₁ G e) ⁻¹ ∙ (e ◁ β)) ∙
        (isoComp-cong ((isoComp-assoc-at ((comp-assoc x₁ G e) ⁻¹) (e ◁ β) (comp-assoc g x₂ e)) ⁻¹)
          (idIso ((comp-assoc g x₂ e) ⁻¹)) ∙
        isoComp-cong (idIso inner) (transport-identity e x₂ g ∙ isoComp-unitˡ-at _))

    source-normalization : Evaluated.source-evaluation =₂
      ((source-associator ⁻¹) ∙ input-associator ⁻¹)
    source-normalization = isoComp-cong (transport-identity (e ∘ x₂) g f)
      (transport-identity e x₂ (g ∘ f))

    target-normalization : Evaluated.target-evaluation =₂
      ((target-associator ⁻¹ ▷ x₀) ∙ output-associator ⁻¹)
    target-normalization = isoComp-cong (preWhisker x₀ ◁ transport-identity e G F) (idIso _)

    action-normalization : Evaluated.evaluation-action =₂ action
    action-normalization =
      (isoComp-assoc-at ((comp-assoc x₀ F (e ∘ G)) ⁻¹)
        (((e ∘ G) ◁ α) ∙ comp-assoc f x₁ (e ∘ G)) (inner ▷ f)) ⁻¹ ∙
      isoComp-cong (idIso ((comp-assoc x₀ F (e ∘ G)) ⁻¹))
        ((isoComp-assoc-at ((e ∘ G) ◁ α) (comp-assoc f x₁ (e ∘ G)) (inner ▷ f)) ⁻¹)

    projected :
      (((target-associator ⁻¹ ▷ x₀) ∙ output-associator ⁻¹) ∙ (e ◁ paste β α)) =₂
      (action ∙ ((source-associator ⁻¹) ∙ input-associator ⁻¹))
    projected = isoComp-cong action-normalization source-normalization ∙
      (Evaluated.project-paste first-square ∙
        isoComp-cong (target-normalization ⁻¹) (idIso (e ◁ paste β α)))

    comparison : ((target-associator ⁻¹ ▷ x₀) ∙ together) =₂
      (action ∙ source-associator ⁻¹)
    comparison = cancel-inverse-tail (action ∙ source-associator ⁻¹) input-associator ∙
      (isoComp-cong ((isoComp-assoc-at action (source-associator ⁻¹) (input-associator ⁻¹)) ⁻¹)
        (idIso input-associator) ∙
      (isoComp-cong projected (idIso input-associator) ∙
      (isoComp-cong ((isoComp-assoc-at (target-associator ⁻¹ ▷ x₀)
        (output-associator ⁻¹) (e ◁ paste β α)) ⁻¹) (idIso input-associator) ∙
      ((isoComp-assoc-at (target-associator ⁻¹ ▷ x₀)
        ((output-associator ⁻¹) ∙ (e ◁ paste β α)) input-associator) ⁻¹ ∙
        isoComp-cong (idIso (target-associator ⁻¹ ▷ x₀))
          ((isoComp-assoc-at (output-associator ⁻¹) (e ◁ paste β α) input-associator) ⁻¹)))))
```
