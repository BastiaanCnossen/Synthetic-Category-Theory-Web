# Naturality of pasted parameter squares

Replacing a source or target functor by a specified isomorphism changes
the corresponding square by composition with that isomorphism. The pasted
square respects these replacements. We prove the two source and two
target variables separately, then combine them using horizontal
composition's stated definition.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section03.ParameterSquarePasting as ParameterSquarePasting
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section02.Structural as Structural

module SCT.VolumeI.Chapter01.Section03.ParameterSquareNaturality
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open ParameterSquarePasting 𝒯 using (paste)
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (move-square)
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-comp-at; preWhisker-comp-at; whisker-mixed-at)

abstract
  identity-square : {X Y : CAT} {f g : MAP X Y} (α : =₁ f g)
    → =₂ (α ∙ idIso f) (idIso g ∙ α)
  identity-square α = invIso (isoComp-unitˡ-at α) ∙ isoComp-unitʳ-at α

  five-squares : {X Y : CAT}
    {a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄ b₅ : MAP X Y}
    (u : =₁ a₀ a₁) (u′ : =₁ b₀ b₁)
    (v : =₁ a₁ a₂) (v′ : =₁ b₁ b₂)
    (w : =₁ a₂ a₃) (w′ : =₁ b₂ b₃)
    (z : =₁ a₃ a₄) (z′ : =₁ b₃ b₄)
    (t : =₁ a₄ a₅) (t′ : =₁ b₄ b₅)
    (p₀ : =₁ a₀ b₀) (p₁ : =₁ a₁ b₁) (p₂ : =₁ a₂ b₂)
    (p₃ : =₁ a₃ b₃) (p₄ : =₁ a₄ b₄) (p₅ : =₁ a₅ b₅)
    → =₂ (u′ ∙ p₀) (p₁ ∙ u) → =₂ (v′ ∙ p₁) (p₂ ∙ v)
    → =₂ (w′ ∙ p₂) (p₃ ∙ w) → =₂ (z′ ∙ p₃) (p₄ ∙ z)
    → =₂ (t′ ∙ p₄) (p₅ ∙ t)
    → =₂ ((t′ ∙ (z′ ∙ (w′ ∙ (v′ ∙ u′)))) ∙ p₀)
        (p₅ ∙ (t ∙ (z ∙ (w ∙ (v ∙ u)))))
  five-squares u u′ v v′ w w′ z z′ t t′ p₀ p₁ p₂ p₃ p₄ p₅ a b c d e =
    paste-squares (z ∙ (w ∙ (v ∙ u))) (z′ ∙ (w′ ∙ (v′ ∙ u′))) t t′ p₀ p₄ p₅
      (paste-squares (w ∙ (v ∙ u)) (w′ ∙ (v′ ∙ u′)) z z′ p₀ p₃ p₄
        (paste-squares (v ∙ u) (v′ ∙ u′) w w′ p₀ p₂ p₃
          (paste-squares u u′ v v′ p₀ p₁ p₂ a b) c) d) e

  source-inner : {A₀ A₁ A₂ B₀ B₁ B₂ : CAT}
    {f f′ : MAP A₀ A₁} {g : MAP A₁ A₂} {F : MAP B₀ B₁} {G : MAP B₁ B₂}
    {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂}
    (β : =₁ (x₂ ∘ g) (G ∘ x₁))
    (α : =₁ (x₁ ∘ f) (F ∘ x₀)) (α′ : =₁ (x₁ ∘ f′) (F ∘ x₀))
    (η : =₁ f f′) → =₂ (α′ ∙ (x₁ ◁ η)) α
    → =₂ (paste β α′ ∙ (x₂ ◁ (g ◁ η))) (paste β α)
  source-inner {f = f} {f′} {g} {F} {G} {x₀} {x₁} {x₂} β α α′ η square =
    let E = invIso (comp-assoc f g x₂)
        E′ = invIso (comp-assoc f′ g x₂)
        D = β ▷ f
        D′ = β ▷ f′
        C = comp-assoc f x₁ G
        C′ = comp-assoc f′ x₁ G
        B = G ◁ α
        B′ = G ◁ α′
        A = invIso (comp-assoc x₀ F G)
        p₀ = x₂ ◁ (g ◁ η)
        p₁ = (x₂ ∘ g) ◁ η
        p₂ = (G ∘ x₁) ◁ η
        p₃ = G ◁ (x₁ ◁ η)
        pE = move-square (comp-assoc f′ g x₂) p₁ p₀ (comp-assoc f g x₂)
          (postWhisker-comp-at η g x₂)
        pB = invIso (isoComp-unitˡ-at B) ∙
          ((postWhisker G ◁ square) ∙ invIso (postWhisker-isoComp-at G α′ (x₁ ◁ η)))
    in isoComp-unitˡ-at (paste β α) ∙
      five-squares E E′ D D′ C C′ B B′ A A p₀ p₁ p₂ p₃ (idIso _) (idIso _)
        pE (interchange-at β η) (postWhisker-comp-at η x₁ G) pB (identity-square A)

  source-outer : {A₀ A₁ A₂ B₀ B₁ B₂ : CAT}
    {f : MAP A₀ A₁} {g g′ : MAP A₁ A₂} {F : MAP B₀ B₁} {G : MAP B₁ B₂}
    {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂}
    (β : =₁ (x₂ ∘ g) (G ∘ x₁)) (β′ : =₁ (x₂ ∘ g′) (G ∘ x₁))
    (α : =₁ (x₁ ∘ f) (F ∘ x₀)) (θ : =₁ g g′)
    → =₂ (β′ ∙ (x₂ ◁ θ)) β
    → =₂ (paste β′ α ∙ (x₂ ◁ (θ ▷ f))) (paste β α)
  source-outer {f = f} {g} {g′} {F} {G} {x₀} {x₁} {x₂} β β′ α θ square =
    let E = invIso (comp-assoc f g x₂)
        E′ = invIso (comp-assoc f g′ x₂)
        D = β ▷ f
        D′ = β′ ▷ f
        C = comp-assoc f x₁ G
        B = G ◁ α
        A = invIso (comp-assoc x₀ F G)
        p₀ = x₂ ◁ (θ ▷ f)
        p₁ = (x₂ ◁ θ) ▷ f
        pE = move-square (comp-assoc f g′ x₂) p₁ p₀ (comp-assoc f g x₂)
          (whisker-mixed-at θ f x₂)
        pD = invIso (isoComp-unitˡ-at D) ∙
          ((preWhisker f ◁ square) ∙ invIso (preWhisker-isoComp-at β′ (x₂ ◁ θ) f))
    in isoComp-unitˡ-at (paste β α) ∙
      five-squares E E′ D D′ C C B B A A p₀ p₁ (idIso _) (idIso _) (idIso _) (idIso _)
        pE pD (identity-square C) (identity-square B) (identity-square A)

  paste-source-square : {A₀ A₁ A₂ B₀ B₁ B₂ : CAT}
    {f f′ : MAP A₀ A₁} {g g′ : MAP A₁ A₂} {F : MAP B₀ B₁} {G : MAP B₁ B₂}
    {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂}
    (β : =₁ (x₂ ∘ g) (G ∘ x₁)) (β′ : =₁ (x₂ ∘ g′) (G ∘ x₁))
    (α : =₁ (x₁ ∘ f) (F ∘ x₀)) (α′ : =₁ (x₁ ∘ f′) (F ∘ x₀))
    (θ : =₁ g g′) (η : =₁ f f′)
    → =₂ (β′ ∙ (x₂ ◁ θ)) β → =₂ (α′ ∙ (x₁ ◁ η)) α
    → =₂ (paste β′ α′ ∙ (x₂ ◁ (θ ⋆ η))) (paste β α)
  paste-source-square {f′ = f′} {g = g} {x₂ = x₂} β β′ α α′ θ η b a =
    source-inner β α α′ η a ∙
    (isoComp-cong (source-outer β β′ α′ θ b) (idIso (x₂ ◁ (g ◁ η))) ∙
    (invIso (isoComp-assoc-at (paste β′ α′) (x₂ ◁ (θ ▷ f′)) (x₂ ◁ (g ◁ η))) ∙
      isoComp-cong (idIso (paste β′ α′)) (postWhisker-isoComp-at x₂ (θ ▷ f′) (g ◁ η))))

  cancel-source : {X Y : CAT} {f f′ g : MAP X Y}
    (α : =₁ f g) (η : =₁ f f′)
    → =₂ ((α ∙ invIso η) ∙ η) α
  cancel-source α η = isoComp-unitʳ-at α ∙
    (isoComp-cong (idIso α) (isoComp-inverseˡ-at η) ∙ isoComp-assoc-at α (invIso η) η)

  paste-source-normalization : {A₀ A₁ A₂ B₀ B₁ B₂ : CAT}
    {f f′ : MAP A₀ A₁} {g g′ : MAP A₁ A₂} {F : MAP B₀ B₁} {G : MAP B₁ B₂}
    {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂}
    (β : =₁ (x₂ ∘ g) (G ∘ x₁)) (α : =₁ (x₁ ∘ f) (F ∘ x₀))
    (θ : =₁ g g′) (η : =₁ f f′)
    → =₂
        (paste (β ∙ invIso (x₂ ◁ θ)) (α ∙ invIso (x₁ ◁ η)) ∙ (x₂ ◁ (θ ⋆ η)))
        (paste β α)
  paste-source-normalization {x₁ = x₁} {x₂} β α θ η =
    paste-source-square β (β ∙ invIso (x₂ ◁ θ)) α (α ∙ invIso (x₁ ◁ η)) θ η
      (cancel-source β (x₂ ◁ θ)) (cancel-source α (x₁ ◁ η))

  target-inner : {A₀ A₁ A₂ B₀ B₁ B₂ : CAT}
    {f : MAP A₀ A₁} {g : MAP A₁ A₂} {F F′ : MAP B₀ B₁} {G : MAP B₁ B₂}
    {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂}
    (β : =₁ (x₂ ∘ g) (G ∘ x₁)) (α : =₁ (x₁ ∘ f) (F ∘ x₀))
    (φ : =₁ F F′)
    → =₂ (paste β ((φ ▷ x₀) ∙ α)) (((G ◁ φ) ▷ x₀) ∙ paste β α)
  target-inner {f = f} {g} {F} {F′} {G} {x₀} {x₁} {x₂} β α φ =
    let E = invIso (comp-assoc f g x₂)
        D = β ▷ f
        C = comp-assoc f x₁ G
        B = G ◁ α
        B′ = G ◁ ((φ ▷ x₀) ∙ α)
        A = invIso (comp-assoc x₀ F G)
        A′ = invIso (comp-assoc x₀ F′ G)
        p₄ = G ◁ (φ ▷ x₀)
        p₅ = (G ◁ φ) ▷ x₀
        pB = postWhisker-isoComp-at G (φ ▷ x₀) α ∙ isoComp-unitʳ-at B′
        pA = move-square (comp-assoc x₀ F′ G) p₅ p₄ (comp-assoc x₀ F G)
          (whisker-mixed-at φ x₀ G)
    in five-squares E E D D C C B B′ A A′
      (idIso _) (idIso _) (idIso _) (idIso _) p₄ p₅
      (identity-square E) (identity-square D) (identity-square C) pB pA ∙
      invIso (isoComp-unitʳ-at (paste β ((φ ▷ x₀) ∙ α)))

  target-outer : {A₀ A₁ A₂ B₀ B₁ B₂ : CAT}
    {f : MAP A₀ A₁} {g : MAP A₁ A₂} {F : MAP B₀ B₁} {G G′ : MAP B₁ B₂}
    {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂}
    (β : =₁ (x₂ ∘ g) (G ∘ x₁)) (α : =₁ (x₁ ∘ f) (F ∘ x₀))
    (ψ : =₁ G G′)
    → =₂ (paste ((ψ ▷ x₁) ∙ β) α) (((ψ ▷ F) ▷ x₀) ∙ paste β α)
  target-outer {f = f} {g} {F} {G} {G′} {x₀} {x₁} {x₂} β α ψ =
    let E = invIso (comp-assoc f g x₂)
        D = β ▷ f
        D′ = ((ψ ▷ x₁) ∙ β) ▷ f
        C = comp-assoc f x₁ G
        C′ = comp-assoc f x₁ G′
        B = G ◁ α
        B′ = G′ ◁ α
        A = invIso (comp-assoc x₀ F G)
        A′ = invIso (comp-assoc x₀ F G′)
        p₂ = (ψ ▷ x₁) ▷ f
        p₃ = ψ ▷ (x₁ ∘ f)
        p₄ = ψ ▷ (F ∘ x₀)
        p₅ = (ψ ▷ F) ▷ x₀
        pD = preWhisker-isoComp-at (ψ ▷ x₁) β f ∙ isoComp-unitʳ-at D′
        pA = move-square (comp-assoc x₀ F G′) p₅ p₄ (comp-assoc x₀ F G)
          (preWhisker-comp-at ψ F x₀)
    in five-squares E E D D′ C C′ B B′ A A′
      (idIso _) (idIso _) p₂ p₃ p₄ p₅
      (identity-square E) pD (preWhisker-comp-at ψ x₁ f) (invIso (interchange-at ψ α)) pA ∙
      invIso (isoComp-unitʳ-at (paste ((ψ ▷ x₁) ∙ β) α))

  paste-target-normalization : {A₀ A₁ A₂ B₀ B₁ B₂ : CAT}
    {f : MAP A₀ A₁} {g : MAP A₁ A₂} {F F′ : MAP B₀ B₁} {G G′ : MAP B₁ B₂}
    {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂}
    (β : =₁ (x₂ ∘ g) (G ∘ x₁)) (α : =₁ (x₁ ∘ f) (F ∘ x₀))
    (ψ : =₁ G G′) (φ : =₁ F F′)
    → =₂ (paste ((ψ ▷ x₁) ∙ β) ((φ ▷ x₀) ∙ α))
        (((ψ ⋆ φ) ▷ x₀) ∙ paste β α)
  paste-target-normalization {F′ = F′} {G = G} {x₀ = x₀} β α ψ φ =
    isoComp-cong (invIso (preWhisker-isoComp-at (ψ ▷ F′) (G ◁ φ) x₀)) (idIso (paste β α)) ∙
    (invIso (isoComp-assoc-at ((ψ ▷ F′) ▷ x₀) ((G ◁ φ) ▷ x₀) (paste β α)) ∙
    (isoComp-cong (idIso ((ψ ▷ F′) ▷ x₀)) (target-inner β α φ) ∙
      target-outer β ((φ ▷ x₀) ∙ α) ψ))
```
