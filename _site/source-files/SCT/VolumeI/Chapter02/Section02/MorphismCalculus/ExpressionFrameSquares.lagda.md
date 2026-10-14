# Comparing two successive changes of endpoints

Two paths of endpoint changes give identified framed expressions when
their composites are identified. The comparison retains the original
arrow and uses precisely the two supplied endpoint squares.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameSquares
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (retarget-assoc; retarget-cong; retarget-id; restrict-retarget-outer)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Pairing
open Pairing vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

abstract
  retarget-square : {Γ C : CAT} {x y x₁ y₁ x₂ y₂ x₃ y₃ : MAP Γ C}
    (f : MorphismExpression x y) (p : x =₁ x₁) (q : y =₁ y₁)
    (p′ : x =₁ x₂) (q′ : y =₁ y₂)
    (a : x₁ =₁ x₃) (b : y₁ =₁ y₃) (a′ : x₂ =₁ x₃) (b′ : y₂ =₁ y₃) →
    (a ∙ p) =₂ (a′ ∙ p′) → (b ∙ q) =₂ (b′ ∙ q′) →
    ExpressionIso (retarget-expression (retarget-expression f p q) a b)
      (retarget-expression (retarget-expression f p′ q′) a′ b′)
  retarget-square f p q p′ q′ a b a′ b′ source target = expressionIso-compose
    (expressionIso-inverse (retarget-assoc f p′ q′ a′ b′))
    (expressionIso-compose (retarget-cong f source target) (retarget-assoc f p q a b))

  cancel-frames : {Γ C : CAT} {u v u′ v′ : MAP Γ C}
    (f : MorphismExpression u v) (p : u =₁ u′) (q : v =₁ v′)
    (p′ : u′ =₁ u) (q′ : v′ =₁ v) →
    (p′ ∙ p) =₂ idIso u → (q′ ∙ q) =₂ idIso v →
    ExpressionIso (retarget-expression (retarget-expression f p q) p′ q′) f
  cancel-frames f p q p′ q′ source target = expressionIso-compose (retarget-id f)
    (expressionIso-compose (retarget-cong f source target) (retarget-assoc f p q p′ q′))

  restrict-frame-square : {Γ Δ C : CAT} {x y x′ y′ : MAP Γ C}
    (f : MorphismExpression x y) (p : x =₁ x′) (q : y =₁ y′) (h : MAP Δ Γ)
    {a b u v : MAP Δ C}
    (s : (x′ ∘ h) =₁ u) (t : (y′ ∘ h) =₁ v)
    (s′ : (x ∘ h) =₁ a) (t′ : (y ∘ h) =₁ b) (k : a =₁ u) (j : b =₁ v) →
    (s ∙ (p ▷ h)) =₂ (k ∙ s′) → (t ∙ (q ▷ h)) =₂ (j ∙ t′) →
    ExpressionIso (retarget-expression (restrict-expression (retarget-expression f p q) h) s t)
      (retarget-expression (retarget-expression (restrict-expression f h) s′ t′) k j)
  restrict-frame-square f p q h s t s′ t′ k j source target = expressionIso-compose
    (expressionIso-inverse (retarget-assoc (restrict-expression f h) s′ t′ k j))
    (expressionIso-compose (retarget-cong (restrict-expression f h) source target)
      (restrict-retarget-outer f p q h s t))

  restrict-inverse-frames : {Γ Δ C : CAT} {x y x′ y′ : MAP Γ C}
    (f : MorphismExpression x′ y′) (p : x =₁ x′) (q : y =₁ y′) (h : MAP Δ Γ)
    {a b u v : MAP Δ C}
    (s : (x ∘ h) =₁ a) (t : (y ∘ h) =₁ b) (k : a =₁ u) (j : b =₁ v)
    (s′ : (x′ ∘ h) =₁ u) (t′ : (y′ ∘ h) =₁ v) →
    (k ∙ s) =₂ (s′ ∙ (p ▷ h)) → (j ∙ t) =₂ (t′ ∙ (q ▷ h)) →
    ExpressionIso (retarget-expression
      (retarget-expression (restrict-expression (retarget-expression f (p ⁻¹) (q ⁻¹)) h) s t) k j)
      (retarget-expression (restrict-expression f h) s′ t′)
  restrict-inverse-frames f p q h s t k j s′ t′ source target = expressionIso-compose
    (retarget-cong (restrict-expression f h)
      (cancel-right (p ▷ h) s′ ∙ isoComp-cong source (pre-inverse p h))
      (cancel-right (q ▷ h) t′ ∙ isoComp-cong target (pre-inverse q h)))
    (expressionIso-compose (restrict-retarget-outer f (p ⁻¹) (q ⁻¹) h (k ∙ s) (j ∙ t))
      (retarget-assoc (restrict-expression (retarget-expression f (p ⁻¹) (q ⁻¹)) h) s t k j))
```
