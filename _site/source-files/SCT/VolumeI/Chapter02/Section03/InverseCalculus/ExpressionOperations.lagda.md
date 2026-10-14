# Invertibility under operations on morphism expressions

Identity expressions are invertible. An endpoint-preserving identification,
a change of endpoint frames, a restriction of parameters, and
postcomposition by a functor all preserve invertibility. Each assertion
transports the two inverse equations, including their endpoint frames.
No criterion that detects invertibility on objects is used.

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

module SCT.VolumeI.Chapter02.Section03.InverseCalculus.ExpressionOperations
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionExpressions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.UniversalInverseExpressions 𝒯 M ℱ P I E S
  public using (IsInvertibleExpression)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S
  using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionSubstitution 𝒯 M ℱ P I E S
  using (retarget-composition; restrict-composition)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.PostcompositionPresentations 𝒯 M ℱ P I E S
  using (post-composition)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestriction 𝒯 M ℱ I
  using (restrict-expressionIso; restrict-expression-compose; restrict-expression-parameter)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (retarget-cancel)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I
  using (post-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionPostcomposition 𝒯 M ℱ P I E
  using (post-identity)
open import SCT.VolumeI.Chapter02.Section02.ExpressionUnitLaws 𝒯 M ℱ P I E S
  using (left-unit)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionRetargeting as RetargetIdentity
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionSubstitution as RestrictIdentity

identity-invertible : {Γ C : CAT} (x : MAP Γ C) → IsInvertibleExpression (identity-expression x)
identity-invertible x = record
  { right-inverse = identity-expression x
  ; left-inverse = identity-expression x
  ; right-inverse-law = left-unit (identity-expression x)
  ; left-inverse-law = left-unit (identity-expression x) }

identified-invertible : {Γ C : CAT} {x y : MAP Γ C}
  {f g : MorphismExpression x y} → ExpressionIso f g →
  IsInvertibleExpression f → IsInvertibleExpression g
identified-invertible α w = record
  { right-inverse = W.right-inverse
  ; left-inverse = W.left-inverse
  ; right-inverse-law = expressionIso-compose W.right-inverse-law
      (compose-expression-cong (expressionIso-id W.right-inverse) (expressionIso-inverse α))
  ; left-inverse-law = expressionIso-compose W.left-inverse-law
      (compose-expression-cong (expressionIso-inverse α) (expressionIso-id W.left-inverse)) }
  where module W = IsInvertibleExpression w

retarget-invertible : {Γ C : CAT} {x y x′ y′ : MAP Γ C}
  (f : MorphismExpression x y) (p : x =₁ x′) (q : y =₁ y′) →
  IsInvertibleExpression f → IsInvertibleExpression (retarget-expression f p q)
retarget-invertible {x = x} {y} f p q w = record
  { right-inverse = retarget-expression W.right-inverse q p
  ; left-inverse = retarget-expression W.left-inverse q p
  ; right-inverse-law = expressionIso-compose (RetargetIdentity.At.comparison 𝒯 M ℱ P I E q)
      (expressionIso-compose (retarget-expressionIso W.right-inverse-law q q)
        (retarget-composition W.right-inverse f q p q))
  ; left-inverse-law = expressionIso-compose (RetargetIdentity.At.comparison 𝒯 M ℱ P I E p)
      (expressionIso-compose (retarget-expressionIso W.left-inverse-law p p)
        (retarget-composition f W.left-inverse p q p)) }
  where module W = IsInvertibleExpression w

restrict-invertible : {Γ Δ C : CAT} {x y : MAP Γ C}
  (f : MorphismExpression x y) (r : MAP Δ Γ) →
  IsInvertibleExpression f → IsInvertibleExpression (restrict-expression f r)
restrict-invertible {x = x} {y} f r w = record
  { right-inverse = restrict-expression W.right-inverse r
  ; left-inverse = restrict-expression W.left-inverse r
  ; right-inverse-law = expressionIso-compose (RestrictIdentity.Restrict.comparison 𝒯 M ℱ P I E y r)
      (expressionIso-compose (restrict-expressionIso W.right-inverse-law r)
        (restrict-composition W.right-inverse f r))
  ; left-inverse-law = expressionIso-compose (RestrictIdentity.Restrict.comparison 𝒯 M ℱ P I E x r)
      (expressionIso-compose (restrict-expressionIso W.left-inverse-law r)
        (restrict-composition f W.left-inverse r)) }
  where module W = IsInvertibleExpression w

post-invertible : {Γ C D : CAT} (F : MAP C D) {x y : MAP Γ C}
  (f : MorphismExpression x y) →
  IsInvertibleExpression f → IsInvertibleExpression (post-expression F f)
post-invertible F {x} {y} f w = record
  { right-inverse = post-expression F W.right-inverse
  ; left-inverse = post-expression F W.left-inverse
  ; right-inverse-law = expressionIso-compose (post-identity F y)
      (expressionIso-compose (post-expressionIso F W.right-inverse-law)
        (post-composition F W.right-inverse f))
  ; left-inverse-law = expressionIso-compose (post-identity F x)
      (expressionIso-compose (post-expressionIso F W.left-inverse-law)
        (post-composition F f W.left-inverse)) }
  where module W = IsInvertibleExpression w

abstract
  retarget-reflects-invertible : {Γ C : CAT} {x y x′ y′ : MAP Γ C}
    (f : MorphismExpression x y) (p : x =₁ x′) (q : y =₁ y′) →
    IsInvertibleExpression (retarget-expression f p q) → IsInvertibleExpression f
  retarget-reflects-invertible f p q w = identified-invertible (retarget-cancel f p q)
    (retarget-invertible (retarget-expression f p q) (p ⁻¹) (q ⁻¹) w)

  restrict-composite-invertible : {Γ Δ Θ C : CAT} {x y : MAP Γ C}
    (f : MorphismExpression x y) (r : MAP Δ Γ) (s : MAP Θ Δ) →
    IsInvertibleExpression (restrict-expression f r) →
    IsInvertibleExpression (restrict-expression f (r ∘ s))
  restrict-composite-invertible {x = x} {y} f r s w =
    identified-invertible (restrict-expression-compose f r s)
      (retarget-invertible (restrict-expression (restrict-expression f r) s)
        (comp-assoc s r x) (comp-assoc s r y)
        (restrict-invertible (restrict-expression f r) s w))

  restrict-parameter-invertible : {Γ Δ C : CAT} {x y : MAP Γ C}
    (f : MorphismExpression x y) {r s : MAP Δ Γ} (α : r =₁ s) →
    IsInvertibleExpression (restrict-expression f r) →
    IsInvertibleExpression (restrict-expression f s)
  restrict-parameter-invertible {x = x} {y} f α w =
    identified-invertible (restrict-expression-parameter f α)
      (retarget-invertible (restrict-expression f _) (x ◁ α) (y ◁ α) w)

```
