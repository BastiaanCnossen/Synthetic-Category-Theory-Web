# Unit and counit formulas with restricted endpoints

Transposition is composition with the restricted unit followed by the
functorial image of the original family. In the reverse direction it is
the functorial image followed by the restricted counit. The associators in the image
are specified explicitly. The unit and counit restriction comparisons supply the
required coherence, including both endpoint frames.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeFamilyFormula
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (retarget-assoc; retarget-cong; retarget-id; post-retarget)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S
  using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionSubstitution 𝒯 M ℱ P I E S
  using (retarget-composition)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-composite)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeFamilies as Families
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.ComponentRestriction as Components

private
  abstract
    inverse-composite-cancel : {X Y : CAT} {h j k : MAP X Y}
      (α : j =₁ k) (β : h =₁ j) → (((α ∙ β) ⁻¹) ∙ α) =₂ (β ⁻¹)
    inverse-composite-cancel α β = isoComp-unitʳ-at (β ⁻¹) ∙
      (isoComp-cong (idIso (β ⁻¹)) (isoComp-inverseˡ-at α) ∙
        (isoComp-assoc-at (β ⁻¹) (α ⁻¹) α ∙
          isoComp-cong (inverse-composite α β) (idIso α)))

module At {B C D : CAT} {l : MAP C D} {r : MAP D C}
  (adj : Adjunction l r) (x : MAP B C) (y : MAP B D) where
  private
    module A = Adjunction adj using (unit-at; transpose; counit-at; untranspose)
    module F = Families.Families 𝒯 M ℱ P I E S adj x y using (forward; left-normal; backward; right-normal)
    module U = Components.Components 𝒯 M ℱ P I E S adj using (unit-restrict; counit-restrict)

  module Family {Γ : CAT} (b : MAP Γ B)
    (f : MorphismExpression ((l ∘ x) ∘ b) (y ∘ b)) where
    private
      α = comp-assoc b x l
      β = comp-assoc b (l ∘ x) r
      γ = comp-assoc b y r
      κ = (r ◁ α) ∙ β
      unit = A.unit-at (x ∘ b)
      mapped = post-expression r (F.left-normal b f)

    unit-family : MorphismExpression (x ∘ b) ((r ∘ (l ∘ x)) ∘ b)
    unit-family = restrict-expression (A.unit-at x) b

    image-family : MorphismExpression ((r ∘ (l ∘ x)) ∘ b) ((r ∘ y) ∘ b)
    image-family = retarget-expression (post-expression r f) (β ⁻¹) (γ ⁻¹)

    private
      abstract
        unit-comparison : ExpressionIso
          (retarget-expression unit (idIso (x ∘ b)) (κ ⁻¹)) unit-family
        unit-comparison = expressionIso-compose (retarget-id unit-family)
          (expressionIso-compose
            (retarget-cong unit-family (isoComp-unitˡ-at (idIso (x ∘ b))) (isoComp-inverseˡ-at κ))
            (expressionIso-compose
              (retarget-assoc unit-family (idIso (x ∘ b)) κ (idIso (x ∘ b)) (κ ⁻¹))
              (retarget-expressionIso (expressionIso-inverse (U.unit-restrict x b))
                (idIso (x ∘ b)) (κ ⁻¹))))

        image-comparison : ExpressionIso
          (retarget-expression mapped (κ ⁻¹) (γ ⁻¹)) image-family
        image-comparison = expressionIso-compose
          (retarget-cong (post-expression r f)
            (inverse-composite-cancel (r ◁ α) β)
            (isoComp-unitʳ-at (γ ⁻¹) ∙
              isoComp-cong (idIso (γ ⁻¹)) (postWhisker-idIso r (y ∘ b))))
          (expressionIso-compose
            (retarget-assoc (post-expression r f) (r ◁ α) (r ◁ idIso (y ∘ b)) (κ ⁻¹) (γ ⁻¹))
            (retarget-expressionIso (post-retarget r f α (idIso (y ∘ b))) (κ ⁻¹) (γ ⁻¹)))

    abstract
      comparison : ExpressionIso (F.forward b f) (compose-expression unit-family image-family)
      comparison = expressionIso-compose
        (compose-expression-cong unit-comparison image-comparison)
        (expressionIso-inverse (retarget-composition unit mapped (idIso (x ∘ b)) (κ ⁻¹) (γ ⁻¹)))

  module BackwardFamily {Γ : CAT} (b : MAP Γ B)
    (f : MorphismExpression (x ∘ b) ((r ∘ y) ∘ b)) where
    private
      α = comp-assoc b x l
      β = comp-assoc b (r ∘ y) l
      γ = comp-assoc b y r
      κ = (l ◁ γ) ∙ β
      counit = A.counit-at (y ∘ b)
      mapped = post-expression l (F.right-normal b f)

    image-family : MorphismExpression ((l ∘ x) ∘ b) ((l ∘ (r ∘ y)) ∘ b)
    image-family = retarget-expression (post-expression l f) (α ⁻¹) (β ⁻¹)

    counit-family : MorphismExpression ((l ∘ (r ∘ y)) ∘ b) (y ∘ b)
    counit-family = restrict-expression (A.counit-at y) b

    private
      abstract
        image-comparison : ExpressionIso
          (retarget-expression mapped (α ⁻¹) (κ ⁻¹)) image-family
        image-comparison = expressionIso-compose
          (retarget-cong (post-expression l f)
            (isoComp-unitʳ-at (α ⁻¹) ∙
              isoComp-cong (idIso (α ⁻¹)) (postWhisker-idIso l (x ∘ b)))
            (inverse-composite-cancel (l ◁ γ) β))
          (expressionIso-compose
            (retarget-assoc (post-expression l f) (l ◁ idIso (x ∘ b)) (l ◁ γ) (α ⁻¹) (κ ⁻¹))
            (retarget-expressionIso (post-retarget l f (idIso (x ∘ b)) γ) (α ⁻¹) (κ ⁻¹)))

        counit-comparison : ExpressionIso
          (retarget-expression counit (κ ⁻¹) (idIso (y ∘ b))) counit-family
        counit-comparison = expressionIso-compose (retarget-id counit-family)
          (expressionIso-compose
            (retarget-cong counit-family (isoComp-inverseˡ-at κ) (isoComp-unitˡ-at (idIso (y ∘ b))))
            (expressionIso-compose
              (retarget-assoc counit-family κ (idIso (y ∘ b)) (κ ⁻¹) (idIso (y ∘ b)))
              (retarget-expressionIso (expressionIso-inverse (U.counit-restrict y b))
                (κ ⁻¹) (idIso (y ∘ b)))))

    abstract
      comparison : ExpressionIso (F.backward b f) (compose-expression image-family counit-family)
      comparison = expressionIso-compose
        (compose-expression-cong image-comparison counit-comparison)
        (expressionIso-inverse (retarget-composition mapped counit (α ⁻¹) (κ ⁻¹) (idIso (y ∘ b))))
```
