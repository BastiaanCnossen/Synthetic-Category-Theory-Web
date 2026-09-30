# Normalized operations after uncurrying

These comparison rules combine evaluation with a specified change of
endpoints. They let later triangle proofs use one common frame throughout.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingFramedOperations
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingExpressions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (retarget-assoc; retarget-cong; post-retarget; restrict-retarget)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I using (post-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestriction 𝒯 M ℱ I using (restrict-expressionIso)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingFunctorPostcomposition as Post
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingExpressionRestriction as Restrict
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingExpressionFrames as Frames

module At {Γ K C : CAT} {f g : MAP Γ (Fun K C)} (α : MorphismExpression f g)
  {h k : MAP (Γ × K) C} (p : funUncurry f =₁ h) (q : funUncurry g =₁ k)
  {β : MorphismExpression h k} (ξ : ExpressionIso (retarget-expression (uncurry-expression α) p q) β) where

  abstract
    post : {D : CAT} (F : MAP C D) →
      ExpressionIso (retarget-expression (uncurry-expression (post-expression (funPost F) α))
        ((F ◁ p) ∙ funPost-uncurry F f) ((F ◁ q) ∙ funPost-uncurry F g)) (post-expression F β)
    post F = expressionIso-compose (post-expressionIso F ξ)
      (expressionIso-compose (expressionIso-inverse (post-retarget F (uncurry-expression α) p q))
        (expressionIso-compose (retarget-expressionIso (Post.At.value 𝒯 M ℱ P I E S F α) (F ◁ p) (F ◁ q))
          (expressionIso-inverse (retarget-assoc (uncurry-expression (post-expression (funPost F) α))
            (funPost-uncurry F f) (funPost-uncurry F g) (F ◁ p) (F ◁ q)))))

    restrict : {Δ : CAT} (r : MAP Δ Γ) →
      let σ = productMap r (id K) in
      ExpressionIso (retarget-expression (uncurry-expression (restrict-expression α r))
        ((p ▷ σ) ∙ funUncurry-restrict f r) ((q ▷ σ) ∙ funUncurry-restrict g r))
        (restrict-expression β σ)
    restrict {Δ} r = expressionIso-compose (restrict-expressionIso ξ σ)
      (expressionIso-compose (expressionIso-inverse (restrict-retarget (uncurry-expression α) p q σ))
        (expressionIso-compose (retarget-expressionIso (Restrict.At.comparison 𝒯 M ℱ P I E S α r) (p ▷ σ) (q ▷ σ))
          (expressionIso-inverse (retarget-assoc (uncurry-expression (restrict-expression α r))
            (funUncurry-restrict f r) (funUncurry-restrict g r) (p ▷ σ) (q ▷ σ)))))
      where
      σ : MAP (Δ × K) (Γ × K)
      σ = productMap r (id K)

    retarget : {f′ g′ : MAP Γ (Fun K C)} (a : f =₁ f′) (b : g =₁ g′)
      (p′ : funUncurry f′ =₁ h) (q′ : funUncurry g′ =₁ k) →
      (p′ ∙ funUncurryIso a) =₂ p → (q′ ∙ funUncurryIso b) =₂ q →
      ExpressionIso (retarget-expression (uncurry-expression (retarget-expression α a b)) p′ q′) β
    retarget a b p′ q′ ep eq = expressionIso-compose ξ
      (expressionIso-compose (retarget-cong (uncurry-expression α) ep eq)
        (expressionIso-compose (retarget-assoc (uncurry-expression α) (funUncurryIso a) (funUncurryIso b) p′ q′)
          (retarget-expressionIso (Frames.At.value 𝒯 M ℱ P I E S α a b) p′ q′)))
```
