# Naturality of pasted parameter squares

Replacing a source or target functor by a specified isomorphism changes
the corresponding square by composition with that isomorphism. The pasted
square respects these replacements. We prove the two source and two
target variables separately, then combine them using horizontal
composition's stated definition.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Substitution.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ParameterSquarePasting as ParameterSquarePasting
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.FunctorCoherence as FunctorCoherence
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

module SCT.VolumeI.Chapter01.Section04.SquareCalculus.ParameterSquareNaturality
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open ParameterSquarePasting 𝒯 using (paste)
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (move-square)
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-comp-at; preWhisker-comp-at; whisker-mixed-at)

open FunctorCoherence vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (hcomp-idOuter; hcomp-idInner)

abstract
  identity-square : {X Y : CAT} {f g : MAP X Y} (α : f =₁ g)
    → (α ∙ idIso f) =₂ (idIso g ∙ α)
  identity-square α = (isoComp-unitˡ-at α) ⁻¹ ∙ isoComp-unitʳ-at α

  five-squares : {X Y : CAT}
    {a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄ b₅ : MAP X Y}
    (u : a₀ =₁ a₁) (u′ : b₀ =₁ b₁)
    (v : a₁ =₁ a₂) (v′ : b₁ =₁ b₂)
    (w : a₂ =₁ a₃) (w′ : b₂ =₁ b₃)
    (z : a₃ =₁ a₄) (z′ : b₃ =₁ b₄)
    (t : a₄ =₁ a₅) (t′ : b₄ =₁ b₅)
    (p₀ : a₀ =₁ b₀) (p₁ : a₁ =₁ b₁) (p₂ : a₂ =₁ b₂)
    (p₃ : a₃ =₁ b₃) (p₄ : a₄ =₁ b₄) (p₅ : a₅ =₁ b₅)
    → (u′ ∙ p₀) =₂ (p₁ ∙ u) → (v′ ∙ p₁) =₂ (p₂ ∙ v)
    → (w′ ∙ p₂) =₂ (p₃ ∙ w) → (z′ ∙ p₃) =₂ (p₄ ∙ z)
    → (t′ ∙ p₄) =₂ (p₅ ∙ t)
    → ((t′ ∙ (z′ ∙ (w′ ∙ (v′ ∙ u′)))) ∙ p₀) =₂
        (p₅ ∙ (t ∙ (z ∙ (w ∙ (v ∙ u)))))
  five-squares u u′ v v′ w w′ z z′ t t′ p₀ p₁ p₂ p₃ p₄ p₅ a b c d e =
    paste-squares (z ∙ (w ∙ (v ∙ u))) (z′ ∙ (w′ ∙ (v′ ∙ u′))) t t′ p₀ p₄ p₅
      (paste-squares (w ∙ (v ∙ u)) (w′ ∙ (v′ ∙ u′)) z z′ p₀ p₃ p₄
        (paste-squares (v ∙ u) (v′ ∙ u′) w w′ p₀ p₂ p₃
          (paste-squares u u′ v v′ p₀ p₁ p₂ a b) c) d) e

  source-inner : {A₀ A₁ A₂ B₀ B₁ B₂ : CAT}
    {f f′ : MAP A₀ A₁} {g : MAP A₁ A₂} {F : MAP B₀ B₁} {G : MAP B₁ B₂}
    {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂}
    (β : (x₂ ∘ g) =₁ (G ∘ x₁))
    (α : (x₁ ∘ f) =₁ (F ∘ x₀)) (α′ : (x₁ ∘ f′) =₁ (F ∘ x₀))
    (η : f =₁ f′) → (α′ ∙ (x₁ ◁ η)) =₂ α
    → (paste β α′ ∙ (x₂ ◁ (g ◁ η))) =₂ (paste β α)
  source-inner {f = f} {f′} {g} {F} {G} {x₀} {x₁} {x₂} β α α′ η square =
    let E = (comp-assoc f g x₂) ⁻¹
        E′ = (comp-assoc f′ g x₂) ⁻¹
        D = β ▷ f
        D′ = β ▷ f′
        C = comp-assoc f x₁ G
        C′ = comp-assoc f′ x₁ G
        B = G ◁ α
        B′ = G ◁ α′
        A = (comp-assoc x₀ F G) ⁻¹
        p₀ = x₂ ◁ (g ◁ η)
        p₁ = (x₂ ∘ g) ◁ η
        p₂ = (G ∘ x₁) ◁ η
        p₃ = G ◁ (x₁ ◁ η)
        pE = move-square (comp-assoc f′ g x₂) p₁ p₀ (comp-assoc f g x₂)
          (postWhisker-comp-at η g x₂)
        pB = (isoComp-unitˡ-at B) ⁻¹ ∙
          ((postWhisker G ◁ square) ∙ (postWhisker-isoComp-at G α′ (x₁ ◁ η)) ⁻¹)
    in isoComp-unitˡ-at (paste β α) ∙
      five-squares E E′ D D′ C C′ B B′ A A p₀ p₁ p₂ p₃ (idIso _) (idIso _)
        pE (interchange-at β η) (postWhisker-comp-at η x₁ G) pB (identity-square A)

  source-outer : {A₀ A₁ A₂ B₀ B₁ B₂ : CAT}
    {f : MAP A₀ A₁} {g g′ : MAP A₁ A₂} {F : MAP B₀ B₁} {G : MAP B₁ B₂}
    {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂}
    (β : (x₂ ∘ g) =₁ (G ∘ x₁)) (β′ : (x₂ ∘ g′) =₁ (G ∘ x₁))
    (α : (x₁ ∘ f) =₁ (F ∘ x₀)) (θ : g =₁ g′)
    → (β′ ∙ (x₂ ◁ θ)) =₂ β
    → (paste β′ α ∙ (x₂ ◁ (θ ▷ f))) =₂ (paste β α)
  source-outer {f = f} {g} {g′} {F} {G} {x₀} {x₁} {x₂} β β′ α θ square =
    let E = (comp-assoc f g x₂) ⁻¹
        E′ = (comp-assoc f g′ x₂) ⁻¹
        D = β ▷ f
        D′ = β′ ▷ f
        C = comp-assoc f x₁ G
        B = G ◁ α
        A = (comp-assoc x₀ F G) ⁻¹
        p₀ = x₂ ◁ (θ ▷ f)
        p₁ = (x₂ ◁ θ) ▷ f
        pE = move-square (comp-assoc f g′ x₂) p₁ p₀ (comp-assoc f g x₂)
          (whisker-mixed-at θ f x₂)
        pD = (isoComp-unitˡ-at D) ⁻¹ ∙
          ((preWhisker f ◁ square) ∙ (preWhisker-isoComp-at β′ (x₂ ◁ θ) f) ⁻¹)
    in isoComp-unitˡ-at (paste β α) ∙
      five-squares E E′ D D′ C C B B A A p₀ p₁ (idIso _) (idIso _) (idIso _) (idIso _)
        pE pD (identity-square C) (identity-square B) (identity-square A)

  paste-source-square : {A₀ A₁ A₂ B₀ B₁ B₂ : CAT}
    {f f′ : MAP A₀ A₁} {g g′ : MAP A₁ A₂} {F : MAP B₀ B₁} {G : MAP B₁ B₂}
    {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂}
    (β : (x₂ ∘ g) =₁ (G ∘ x₁)) (β′ : (x₂ ∘ g′) =₁ (G ∘ x₁))
    (α : (x₁ ∘ f) =₁ (F ∘ x₀)) (α′ : (x₁ ∘ f′) =₁ (F ∘ x₀))
    (θ : g =₁ g′) (η : f =₁ f′)
    → (β′ ∙ (x₂ ◁ θ)) =₂ β → (α′ ∙ (x₁ ◁ η)) =₂ α
    → (paste β′ α′ ∙ (x₂ ◁ (θ ⋆ η))) =₂ (paste β α)
  paste-source-square {f′ = f′} {g = g} {x₂ = x₂} β β′ α α′ θ η b a =
    source-inner β α α′ η a ∙
    (isoComp-cong (source-outer β β′ α′ θ b) (idIso (x₂ ◁ (g ◁ η))) ∙
    ((isoComp-assoc-at (paste β′ α′) (x₂ ◁ (θ ▷ f′)) (x₂ ◁ (g ◁ η))) ⁻¹ ∙
      isoComp-cong (idIso (paste β′ α′)) (postWhisker-isoComp-at x₂ (θ ▷ f′) (g ◁ η))))

  cancel-source : {X Y : CAT} {f f′ g : MAP X Y}
    (α : f =₁ g) (η : f =₁ f′)
    → ((α ∙ η ⁻¹) ∙ η) =₂ α
  cancel-source α η = isoComp-unitʳ-at α ∙
    (isoComp-cong (idIso α) (isoComp-inverseˡ-at η) ∙ isoComp-assoc-at α (η ⁻¹) η)

  paste-source-normalization : {A₀ A₁ A₂ B₀ B₁ B₂ : CAT}
    {f f′ : MAP A₀ A₁} {g g′ : MAP A₁ A₂} {F : MAP B₀ B₁} {G : MAP B₁ B₂}
    {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂}
    (β : (x₂ ∘ g) =₁ (G ∘ x₁)) (α : (x₁ ∘ f) =₁ (F ∘ x₀))
    (θ : g =₁ g′) (η : f =₁ f′)
    →
        (paste (β ∙ (x₂ ◁ θ) ⁻¹) (α ∙ (x₁ ◁ η) ⁻¹) ∙ (x₂ ◁ (θ ⋆ η))) =₂
        (paste β α)
  paste-source-normalization {x₁ = x₁} {x₂} β α θ η =
    paste-source-square β (β ∙ (x₂ ◁ θ) ⁻¹) α (α ∙ (x₁ ◁ η) ⁻¹) θ η
      (cancel-source β (x₂ ◁ θ)) (cancel-source α (x₁ ◁ η))

  target-inner : {A₀ A₁ A₂ B₀ B₁ B₂ : CAT}
    {f : MAP A₀ A₁} {g : MAP A₁ A₂} {F F′ : MAP B₀ B₁} {G : MAP B₁ B₂}
    {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂}
    (β : (x₂ ∘ g) =₁ (G ∘ x₁)) (α : (x₁ ∘ f) =₁ (F ∘ x₀))
    (φ : F =₁ F′)
    → (paste β ((φ ▷ x₀) ∙ α)) =₂ (((G ◁ φ) ▷ x₀) ∙ paste β α)
  target-inner {f = f} {g} {F} {F′} {G} {x₀} {x₁} {x₂} β α φ =
    let E = (comp-assoc f g x₂) ⁻¹
        D = β ▷ f
        C = comp-assoc f x₁ G
        B = G ◁ α
        B′ = G ◁ ((φ ▷ x₀) ∙ α)
        A = (comp-assoc x₀ F G) ⁻¹
        A′ = (comp-assoc x₀ F′ G) ⁻¹
        p₄ = G ◁ (φ ▷ x₀)
        p₅ = (G ◁ φ) ▷ x₀
        pB = postWhisker-isoComp-at G (φ ▷ x₀) α ∙ isoComp-unitʳ-at B′
        pA = move-square (comp-assoc x₀ F′ G) p₅ p₄ (comp-assoc x₀ F G)
          (whisker-mixed-at φ x₀ G)
    in five-squares E E D D C C B B′ A A′
      (idIso _) (idIso _) (idIso _) (idIso _) p₄ p₅
      (identity-square E) (identity-square D) (identity-square C) pB pA ∙
      (isoComp-unitʳ-at (paste β ((φ ▷ x₀) ∙ α))) ⁻¹

  target-outer : {A₀ A₁ A₂ B₀ B₁ B₂ : CAT}
    {f : MAP A₀ A₁} {g : MAP A₁ A₂} {F : MAP B₀ B₁} {G G′ : MAP B₁ B₂}
    {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂}
    (β : (x₂ ∘ g) =₁ (G ∘ x₁)) (α : (x₁ ∘ f) =₁ (F ∘ x₀))
    (ψ : G =₁ G′)
    → (paste ((ψ ▷ x₁) ∙ β) α) =₂ (((ψ ▷ F) ▷ x₀) ∙ paste β α)
  target-outer {f = f} {g} {F} {G} {G′} {x₀} {x₁} {x₂} β α ψ =
    let E = (comp-assoc f g x₂) ⁻¹
        D = β ▷ f
        D′ = ((ψ ▷ x₁) ∙ β) ▷ f
        C = comp-assoc f x₁ G
        C′ = comp-assoc f x₁ G′
        B = G ◁ α
        B′ = G′ ◁ α
        A = (comp-assoc x₀ F G) ⁻¹
        A′ = (comp-assoc x₀ F G′) ⁻¹
        p₂ = (ψ ▷ x₁) ▷ f
        p₃ = ψ ▷ (x₁ ∘ f)
        p₄ = ψ ▷ (F ∘ x₀)
        p₅ = (ψ ▷ F) ▷ x₀
        pD = preWhisker-isoComp-at (ψ ▷ x₁) β f ∙ isoComp-unitʳ-at D′
        pA = move-square (comp-assoc x₀ F G′) p₅ p₄ (comp-assoc x₀ F G)
          (preWhisker-comp-at ψ F x₀)
    in five-squares E E D D′ C C′ B B′ A A′
      (idIso _) (idIso _) p₂ p₃ p₄ p₅
      (identity-square E) pD (preWhisker-comp-at ψ x₁ f) ((interchange-at ψ α) ⁻¹) pA ∙
      (isoComp-unitʳ-at (paste ((ψ ▷ x₁) ∙ β) α)) ⁻¹

  paste-target-normalization : {A₀ A₁ A₂ B₀ B₁ B₂ : CAT}
    {f : MAP A₀ A₁} {g : MAP A₁ A₂} {F F′ : MAP B₀ B₁} {G G′ : MAP B₁ B₂}
    {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂}
    (β : (x₂ ∘ g) =₁ (G ∘ x₁)) (α : (x₁ ∘ f) =₁ (F ∘ x₀))
    (ψ : G =₁ G′) (φ : F =₁ F′)
    → (paste ((ψ ▷ x₁) ∙ β) ((φ ▷ x₀) ∙ α)) =₂
        (((ψ ⋆ φ) ▷ x₀) ∙ paste β α)
  paste-target-normalization {F′ = F′} {G = G} {x₀ = x₀} β α ψ φ =
    isoComp-cong ((preWhisker-isoComp-at (ψ ▷ F′) (G ◁ φ) x₀) ⁻¹) (idIso (paste β α)) ∙
    ((isoComp-assoc-at ((ψ ▷ F′) ▷ x₀) ((G ◁ φ) ▷ x₀) (paste β α)) ⁻¹ ∙
    (isoComp-cong (idIso ((ψ ▷ F′) ▷ x₀)) (target-inner β α φ) ∙
      target-outer β ((φ ▷ x₀) ∙ α) ψ))
```


Pasting respects simultaneous specified comparisons on both sides of the
parameter squares. When one pair of functors is unchanged, the horizontal
identity comparisons give the two whiskering forms below. These are useful
for both the associator and the unit comparisons, without requiring a
mapping-anima parameter.

```agda
opaque
  paste-natural : {A₀ A₁ A₂ B₀ B₁ B₂ : CAT}
    {f f′ : MAP A₀ A₁} {g g′ : MAP A₁ A₂} {F F′ : MAP B₀ B₁} {G G′ : MAP B₁ B₂}
    {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂}
    (β : (x₂ ∘ g) =₁ (G ∘ x₁)) (β′ : (x₂ ∘ g′) =₁ (G′ ∘ x₁))
    (α : (x₁ ∘ f) =₁ (F ∘ x₀)) (α′ : (x₁ ∘ f′) =₁ (F′ ∘ x₀))
    (θ : g =₁ g′) (η : f =₁ f′) (ψ : G =₁ G′) (φ : F =₁ F′)
    → ((ψ ▷ x₁) ∙ β) =₂ (β′ ∙ (x₂ ◁ θ))
    → ((φ ▷ x₀) ∙ α) =₂ (α′ ∙ (x₁ ◁ η))
    → (((ψ ⋆ φ) ▷ x₀) ∙ paste β α) =₂ (paste β′ α′ ∙ (x₂ ◁ (θ ⋆ η)))
  paste-natural {x₀ = x₀} {x₁} β β′ α α′ θ η ψ φ b a =
    (paste-target-normalization β α ψ φ ∙
      paste-source-square ((ψ ▷ x₁) ∙ β) β′ ((φ ▷ x₀) ∙ α) α′ θ η (b ⁻¹) (a ⁻¹)) ⁻¹

  unchanged-parameter-square : {A B C D : CAT}
    {f : MAP A B} {F : MAP C D} {x : MAP A C} {y : MAP B D}
    (α : (y ∘ f) =₁ (F ∘ x))
    → ((idIso F ▷ x) ∙ α) =₂ (α ∙ (y ◁ idIso f))
  unchanged-parameter-square {f = f} {F} {x} {y} α =
    isoComp-cong (idIso α) ((postWhisker-idIso y f) ⁻¹) ∙
    ((isoComp-unitʳ-at α) ⁻¹ ∙
    (isoComp-unitˡ-at α ∙ isoComp-cong (preWhisker-idIso F x) (idIso α)))

  paste-natural-outer : {A₀ A₁ A₂ B₀ B₁ B₂ : CAT}
    {f : MAP A₀ A₁} {g g′ : MAP A₁ A₂} {F : MAP B₀ B₁} {G G′ : MAP B₁ B₂}
    {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂}
    (β : (x₂ ∘ g) =₁ (G ∘ x₁)) (β′ : (x₂ ∘ g′) =₁ (G′ ∘ x₁))
    (α : (x₁ ∘ f) =₁ (F ∘ x₀)) (θ : g =₁ g′) (ψ : G =₁ G′)
    → ((ψ ▷ x₁) ∙ β) =₂ (β′ ∙ (x₂ ◁ θ))
    → (((ψ ▷ F) ▷ x₀) ∙ paste β α) =₂
        (paste β′ α ∙ (x₂ ◁ (θ ▷ f)))
  paste-natural-outer {f = f} {g} {g′} {F} {G} {G′} {x₀} {x₁} {x₂} β β′ α θ ψ square =
    isoComp-cong (idIso (paste β′ α)) (postWhisker x₂ ◁ hcomp-idInner θ f) ∙
      (paste-natural {f = f} {f′ = f} {g = g} {g′ = g′}
        {F = F} {F′ = F} {G = G} {G′ = G′} {x₀ = x₀} {x₁ = x₁} {x₂ = x₂}
        β β′ α α θ (idIso f) ψ (idIso F) square (unchanged-parameter-square α) ∙
        isoComp-cong (preWhisker x₀ ◁ (hcomp-idInner ψ F) ⁻¹) (idIso (paste β α)))

  paste-natural-inner : {A₀ A₁ A₂ B₀ B₁ B₂ : CAT}
    {f f′ : MAP A₀ A₁} {g : MAP A₁ A₂} {F F′ : MAP B₀ B₁} {G : MAP B₁ B₂}
    {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂}
    (β : (x₂ ∘ g) =₁ (G ∘ x₁))
    (α : (x₁ ∘ f) =₁ (F ∘ x₀)) (α′ : (x₁ ∘ f′) =₁ (F′ ∘ x₀))
    (η : f =₁ f′) (φ : F =₁ F′)
    → ((φ ▷ x₀) ∙ α) =₂ (α′ ∙ (x₁ ◁ η))
    → (((G ◁ φ) ▷ x₀) ∙ paste β α) =₂
        (paste β α′ ∙ (x₂ ◁ (g ◁ η)))
  paste-natural-inner {f = f} {f′} {g} {F} {F′} {G} {x₀} {x₁} {x₂} β α α′ η φ square =
    isoComp-cong (idIso (paste β α′)) (postWhisker x₂ ◁ hcomp-idOuter g η) ∙
      (paste-natural {f = f} {f′ = f′} {g = g} {g′ = g}
        {F = F} {F′ = F′} {G = G} {G′ = G} {x₀ = x₀} {x₁ = x₁} {x₂ = x₂}
        β β α α′ (idIso g) η (idIso G) φ (unchanged-parameter-square β) square ∙
        isoComp-cong (preWhisker x₀ ◁ (hcomp-idOuter G φ) ⁻¹) (idIso (paste β α)))


  paste-natural-outer-computation : {A₀ A₁ A₂ B₀ B₁ B₂ : CAT}
    {f : MAP A₀ A₁} {g g′ : MAP A₁ A₂} {F : MAP B₀ B₁} {G G′ : MAP B₁ B₂}
    {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂}
    (β : (x₂ ∘ g) =₁ (G ∘ x₁)) (β′ : (x₂ ∘ g′) =₁ (G′ ∘ x₁))
    (α : (x₁ ∘ f) =₁ (F ∘ x₀)) (θ : g =₁ g′) (ψ : G =₁ G′)
    (square : ((ψ ▷ x₁) ∙ β) =₂ (β′ ∙ (x₂ ◁ θ)))
    → (paste-natural-outer β β′ α θ ψ square) =₃
        (isoComp-cong (idIso (paste β′ α)) (postWhisker x₂ ◁ hcomp-idInner θ f) ∙
          (paste-natural β β′ α α θ (idIso f) ψ (idIso F) square (unchanged-parameter-square α) ∙
            isoComp-cong (preWhisker x₀ ◁ (hcomp-idInner ψ F) ⁻¹) (idIso (paste β α))))
  paste-natural-outer-computation β β′ α θ ψ square = idIso _

  paste-natural-inner-computation : {A₀ A₁ A₂ B₀ B₁ B₂ : CAT}
    {f f′ : MAP A₀ A₁} {g : MAP A₁ A₂} {F F′ : MAP B₀ B₁} {G : MAP B₁ B₂}
    {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂}
    (β : (x₂ ∘ g) =₁ (G ∘ x₁))
    (α : (x₁ ∘ f) =₁ (F ∘ x₀)) (α′ : (x₁ ∘ f′) =₁ (F′ ∘ x₀))
    (η : f =₁ f′) (φ : F =₁ F′)
    (square : ((φ ▷ x₀) ∙ α) =₂ (α′ ∙ (x₁ ◁ η)))
    → (paste-natural-inner β α α′ η φ square) =₃
        (isoComp-cong (idIso (paste β α′)) (postWhisker x₂ ◁ hcomp-idOuter g η) ∙
          (paste-natural β β α α′ (idIso g) η (idIso G) φ (unchanged-parameter-square β) square ∙
            isoComp-cong (preWhisker x₀ ◁ (hcomp-idOuter G φ) ⁻¹) (idIso (paste β α))))
  paste-natural-inner-computation β α α′ η φ square = idIso _
```


For successive comparisons, paste the two naturality squares and then
combine their whiskered boundaries. This fixes the normalization used
when comparing the two parenthesizations of a triple composite.
The named pasting below displays the calculation and gives a concise
computation statement for the packaged comparison.

```agda
comparison-chain-pasting : {A B C D : CAT}
  {f₀ f₁ f₂ : MAP A B} {g₀ g₁ g₂ : MAP C D}
  (s : MAP A C) (t : MAP B D)
  (α : f₀ =₁ f₁) (α′ : g₀ =₁ g₁)
  (β : f₁ =₁ f₂) (β′ : g₁ =₁ g₂)
  (p : (t ∘ f₀) =₁ (g₀ ∘ s))
  (q : (t ∘ f₁) =₁ (g₁ ∘ s))
  (r : (t ∘ f₂) =₁ (g₂ ∘ s))
  → (q ∙ (t ◁ α)) =₂ ((α′ ▷ s) ∙ p)
  → ((β′ ▷ s) ∙ q) =₂ (r ∙ (t ◁ β))
  → (r ∙ (t ◁ (β ∙ α))) =₂ (((β′ ∙ α′) ▷ s) ∙ p)
comparison-chain-pasting s t α α′ β β′ p q r first second =
  isoComp-cong ((preWhisker-isoComp-at β′ α′ s) ⁻¹) (idIso p) ∙
    ((paste-squares (t ◁ α) (α′ ▷ s) (t ◁ β) (β′ ▷ s)
      p q r (first ⁻¹) second) ⁻¹ ∙
      isoComp-cong (idIso r) (postWhisker-isoComp-at t β α))


opaque
  paste-comparison-chain : {A B C D : CAT}
    {f₀ f₁ f₂ : MAP A B} {g₀ g₁ g₂ : MAP C D}
    (s : MAP A C) (t : MAP B D)
    (α : f₀ =₁ f₁) (α′ : g₀ =₁ g₁)
    (β : f₁ =₁ f₂) (β′ : g₁ =₁ g₂)
    (p : (t ∘ f₀) =₁ (g₀ ∘ s))
    (q : (t ∘ f₁) =₁ (g₁ ∘ s))
    (r : (t ∘ f₂) =₁ (g₂ ∘ s))
    → (q ∙ (t ◁ α)) =₂ ((α′ ▷ s) ∙ p)
    → ((β′ ▷ s) ∙ q) =₂ (r ∙ (t ◁ β))
    → (r ∙ (t ◁ (β ∙ α))) =₂ (((β′ ∙ α′) ▷ s) ∙ p)
  paste-comparison-chain s t α α′ β β′ p q r first second =
    comparison-chain-pasting s t α α′ β β′ p q r first second

  paste-comparison-chain-computation : {A B C D : CAT}
    {f₀ f₁ f₂ : MAP A B} {g₀ g₁ g₂ : MAP C D}
    (s : MAP A C) (t : MAP B D)
    (α : f₀ =₁ f₁) (α′ : g₀ =₁ g₁)
    (β : f₁ =₁ f₂) (β′ : g₁ =₁ g₂)
    (p : (t ∘ f₀) =₁ (g₀ ∘ s))
    (q : (t ∘ f₁) =₁ (g₁ ∘ s))
    (r : (t ∘ f₂) =₁ (g₂ ∘ s))
    (first : (q ∙ (t ◁ α)) =₂ ((α′ ▷ s) ∙ p))
    (second : ((β′ ▷ s) ∙ q) =₂ (r ∙ (t ◁ β)))
    → (paste-comparison-chain s t α α′ β β′ p q r first second) =₃
        (comparison-chain-pasting s t α α′ β β′ p q r first second)
  paste-comparison-chain-computation s t α α′ β β′ p q r first second = idIso _
```

When one side of a pasted square is itself compared with a composite,
first paste its comparison with the unchanged side, then combine it with
the given comparison for the whole composite. The two forms distinguish
which side changes; both retain the specified normalization.

```agda
opaque
  paste-comparison-chain-outer : {A₀ A₁ A₂ B₀ B₁ B₂ : CAT}
    {f : MAP A₀ A₁} {g g′ : MAP A₁ A₂} {F : MAP B₀ B₁} {G G′ : MAP B₁ B₂}
    {u : MAP A₀ A₂} {U : MAP B₀ B₂}
    {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂}
    (κ : (x₂ ∘ u) =₁ (U ∘ x₀))
    (β : (x₂ ∘ g) =₁ (G ∘ x₁)) (β′ : (x₂ ∘ g′) =₁ (G′ ∘ x₁))
    (α : (x₁ ∘ f) =₁ (F ∘ x₀))
    (q : u =₁ (g ∘ f)) (p : U =₁ (G ∘ F))
    (θ : g =₁ g′) (ψ : G =₁ G′)
    → (paste β α ∙ (x₂ ◁ q)) =₂ ((p ▷ x₀) ∙ κ)
    → ((ψ ▷ x₁) ∙ β) =₂ (β′ ∙ (x₂ ◁ θ))
    → (paste β′ α ∙ (x₂ ◁ ((θ ▷ f) ∙ q))) =₂
        ((((ψ ▷ F) ∙ p) ▷ x₀) ∙ κ)
  paste-comparison-chain-outer {f = f} {F = F} {x₀ = x₀} {x₂ = x₂}
    κ β β′ α q p θ ψ first second =
    paste-comparison-chain x₀ x₂ q p (θ ▷ f) (ψ ▷ F)
      κ (paste β α) (paste β′ α) first
      (paste-natural-outer β β′ α θ ψ second)

  paste-comparison-chain-inner : {A₀ A₁ A₂ B₀ B₁ B₂ : CAT}
    {f f′ : MAP A₀ A₁} {g : MAP A₁ A₂} {F F′ : MAP B₀ B₁} {G : MAP B₁ B₂}
    {u : MAP A₀ A₂} {U : MAP B₀ B₂}
    {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂}
    (κ : (x₂ ∘ u) =₁ (U ∘ x₀))
    (β : (x₂ ∘ g) =₁ (G ∘ x₁))
    (α : (x₁ ∘ f) =₁ (F ∘ x₀)) (α′ : (x₁ ∘ f′) =₁ (F′ ∘ x₀))
    (q : u =₁ (g ∘ f)) (p : U =₁ (G ∘ F))
    (η : f =₁ f′) (φ : F =₁ F′)
    → (paste β α ∙ (x₂ ◁ q)) =₂ ((p ▷ x₀) ∙ κ)
    → ((φ ▷ x₀) ∙ α) =₂ (α′ ∙ (x₁ ◁ η))
    → (paste β α′ ∙ (x₂ ◁ ((g ◁ η) ∙ q))) =₂
        ((((G ◁ φ) ∙ p) ▷ x₀) ∙ κ)
  paste-comparison-chain-inner {g = g} {G = G} {x₀ = x₀} {x₂ = x₂}
    κ β α α′ q p η φ first second =
    paste-comparison-chain x₀ x₂ q p (g ◁ η) (G ◁ φ)
      κ (paste β α) (paste β α′) first
      (paste-natural-inner β α α′ η φ second)

  paste-comparison-chain-outer-computation : {A₀ A₁ A₂ B₀ B₁ B₂ : CAT}
    {f : MAP A₀ A₁} {g g′ : MAP A₁ A₂} {F : MAP B₀ B₁} {G G′ : MAP B₁ B₂}
    {u : MAP A₀ A₂} {U : MAP B₀ B₂}
    {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂}
    (κ : (x₂ ∘ u) =₁ (U ∘ x₀))
    (β : (x₂ ∘ g) =₁ (G ∘ x₁)) (β′ : (x₂ ∘ g′) =₁ (G′ ∘ x₁))
    (α : (x₁ ∘ f) =₁ (F ∘ x₀))
    (q : u =₁ (g ∘ f)) (p : U =₁ (G ∘ F))
    (θ : g =₁ g′) (ψ : G =₁ G′)
    (first : (paste β α ∙ (x₂ ◁ q)) =₂ ((p ▷ x₀) ∙ κ))
    (second : ((ψ ▷ x₁) ∙ β) =₂ (β′ ∙ (x₂ ◁ θ)))
    → (paste-comparison-chain-outer κ β β′ α q p θ ψ first second) =₃
        (paste-comparison-chain x₀ x₂ q p (θ ▷ f) (ψ ▷ F)
          κ (paste β α) (paste β′ α) first
          (paste-natural-outer β β′ α θ ψ second))
  paste-comparison-chain-outer-computation κ β β′ α q p θ ψ first second = idIso _

  paste-comparison-chain-inner-computation : {A₀ A₁ A₂ B₀ B₁ B₂ : CAT}
    {f f′ : MAP A₀ A₁} {g : MAP A₁ A₂} {F F′ : MAP B₀ B₁} {G : MAP B₁ B₂}
    {u : MAP A₀ A₂} {U : MAP B₀ B₂}
    {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂}
    (κ : (x₂ ∘ u) =₁ (U ∘ x₀))
    (β : (x₂ ∘ g) =₁ (G ∘ x₁))
    (α : (x₁ ∘ f) =₁ (F ∘ x₀)) (α′ : (x₁ ∘ f′) =₁ (F′ ∘ x₀))
    (q : u =₁ (g ∘ f)) (p : U =₁ (G ∘ F))
    (η : f =₁ f′) (φ : F =₁ F′)
    (first : (paste β α ∙ (x₂ ◁ q)) =₂ ((p ▷ x₀) ∙ κ))
    (second : ((φ ▷ x₀) ∙ α) =₂ (α′ ∙ (x₁ ◁ η)))
    → (paste-comparison-chain-inner κ β α α′ q p η φ first second) =₃
        (paste-comparison-chain x₀ x₂ q p (g ◁ η) (G ◁ φ)
          κ (paste β α) (paste β α′) first
          (paste-natural-inner β α α′ η φ second))
  paste-comparison-chain-inner-computation κ β α α′ q p η φ first second = idIso _
```
