# Composition under restriction and changes of endpoints

Apply the corresponding operation to a whole composite presentation.
Segal uniqueness gives the comparison, preserving both outer endpoints.
These statements do not impose coherence on the chosen Segal lifts.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionSubstitution
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositePresentations 𝒯 M ℱ P I E S public
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.PresentationSubstitution as Presentations
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
  using (expressionIso-compose; expressionIso-inverse; retarget-expressionIso)

restrict-composition : {Γ Δ C : CAT} {x y z : MAP Γ C}
  (f : MorphismExpression x y) (g : MorphismExpression y z) (r : MAP Δ Γ) →
  ExpressionIso (compose-expression (restrict-expression f r) (restrict-expression g r))
    (restrict-expression (compose-expression f g) r)
restrict-composition f g r = recognize-composite
  (Presentations.Restrict.value 𝒯 M ℱ P I E S (composition-presentation f g) r)

retarget-composition : {Γ C : CAT} {x y z x′ y′ z′ : MAP Γ C}
  (f : MorphismExpression x y) (g : MorphismExpression y z)
  (α : x =₁ x′) (β : y =₁ y′) (γ : z =₁ z′) →
  ExpressionIso (compose-expression (retarget-expression f α β) (retarget-expression g β γ))
    (retarget-expression (compose-expression f g) α γ)
retarget-composition f g α β γ = recognize-composite
  (Presentations.Retarget.value 𝒯 M ℱ P I E S (composition-presentation f g) α β γ)
```

Restriction followed by specified endpoint frames distributes over a
composite using the same middle frame for both arrows. This packages the
two preceding laws in the orientation used by component calculations.

```agda
restrict-composition-frames : {Γ Δ C : CAT} {x y z : MAP Γ C}
  (f : MorphismExpression x y) (g : MorphismExpression y z) (r : MAP Δ Γ)
  {x′ y′ z′ : MAP Δ C} (p : (x ∘ r) =₁ x′) (q : (y ∘ r) =₁ y′) (t : (z ∘ r) =₁ z′) →
  ExpressionIso (retarget-expression (restrict-expression (compose-expression f g) r) p t)
    (compose-expression (retarget-expression (restrict-expression f r) p q)
      (retarget-expression (restrict-expression g r) q t))
restrict-composition-frames f g r p q t = expressionIso-compose
  (expressionIso-inverse (retarget-composition (restrict-expression f r) (restrict-expression g r) p q t))
  (retarget-expressionIso (expressionIso-inverse (restrict-composition f g r)) p t)
```
