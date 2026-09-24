# The new laws for the global composition functor

The expression proofs transfer to the original composition functor through
`global-composition-comparison`. This comparison retains exactly the global
source and target frames; no endpoints are silently replaced.

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

module SCT.VolumeI.Chapter02.Section02.GlobalCompositionLaws
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.GlobalCompositionExpressions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.ProductExpressions 𝒯 M ℱ I using (pair-expression)
open import SCT.VolumeI.Chapter02.Section02.ProductComposition 𝒯 M ℱ P I E S using (product-composition; pair-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.NaturalTransformationWhiskering 𝒯 M ℱ P I E S using (pre-whisker; post-whisker)
open import SCT.VolumeI.Chapter02.Section02.Interchange 𝒯 M ℱ P I E S using (interchange)
open import SCT.VolumeI.Chapter02.Section02.Naturality 𝒯 M ℱ P I E S using (naturality)
open import SCT.VolumeI.Chapter02.Section02.PrimitiveIdentificationComposition 𝒯 M ℱ P I E S using (identification-composition)

-- Both routes of a comparison use the original global composition.
global-composition-law : {Γ C : CAT} {x y z w : MAP Γ C}
  (f : MorphismExpression x y) (g : MorphismExpression y z)
  (h : MorphismExpression x w) (k : MorphismExpression w z) →
  ExpressionIso (compose-expression f g) (compose-expression h k) →
  ExpressionIso (global-compose-expression f g) (global-compose-expression h k)
global-composition-law f g h k δ = expressionIso-compose
  (expressionIso-inverse (global-composition-comparison h k))
  (expressionIso-compose δ (global-composition-comparison f g))

product-composition-global : {Γ C D : CAT} {x y z : MAP Γ C} {u v w : MAP Γ D}
  (f : MorphismExpression x y) (g : MorphismExpression y z)
  (h : MorphismExpression u v) (k : MorphismExpression v w) →
  ExpressionIso (global-compose-expression (pair-expression f h) (pair-expression g k))
    (pair-expression (global-compose-expression f g) (global-compose-expression h k))
product-composition-global f g h k = expressionIso-compose
  (expressionIso-inverse (pair-expression-cong (global-composition-comparison f g) (global-composition-comparison h k)))
  (expressionIso-compose (product-composition f g h k)
    (global-composition-comparison (pair-expression f h) (pair-expression g k)))

naturality-global : {Γ C D : CAT} {F G : MAP C D} (α : MorphismExpression F G)
  {x y : MAP Γ C} (u : MorphismExpression x y) →
  ExpressionIso
    (global-compose-expression (restrict-expression α x) (post-expression G u))
    (global-compose-expression (post-expression F u) (restrict-expression α y))
naturality-global {F = F} {G} α {x} {y} u = global-composition-law
  (restrict-expression α x) (post-expression G u)
  (post-expression F u) (restrict-expression α y) (naturality α u)

interchange-global : {B C D : CAT} {F G : MAP C D} {u v : MAP B C}
  (α : MorphismExpression (nameFun F) (nameFun G))
  (β : MorphismExpression (nameFun u) (nameFun v)) →
  ExpressionIso (global-compose-expression (pre-whisker u α) (post-whisker G β))
    (global-compose-expression (post-whisker F β) (pre-whisker v α))
interchange-global {F = F} {G} {u} {v} α β = global-composition-law
  (pre-whisker u α) (post-whisker G β) (post-whisker F β) (pre-whisker v α) (interchange α β)

identification-composition-global : {Γ C : CAT} {x y z : MAP Γ C}
  (α : x =₁ y) (β : y =₁ z) →
  ExpressionIso (global-compose-expression (isomorphism-expression α) (isomorphism-expression β))
    (isomorphism-expression (β ∙ α))
identification-composition-global α β = expressionIso-compose (identification-composition α β)
  (global-composition-comparison (isomorphism-expression α) (isomorphism-expression β))
```
