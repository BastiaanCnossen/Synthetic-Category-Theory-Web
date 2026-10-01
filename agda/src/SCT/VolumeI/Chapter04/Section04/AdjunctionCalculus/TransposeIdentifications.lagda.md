# The two transposition formulas are inverse

Naturality moves the counit past the morphism being transposed, and the
left triangle removes the resulting unit-counit pair. The other
composite uses naturality of the unit and the right triangle. Both
calculations are identifications of full framed expressions, uniformly
over an arbitrary absolute parameter category.

These are the inverse equations in the forward implication of
`prop:Adjunctions_Via_Natural_Equivalence_Hom_Groupoids`. The assembly
into the displayed equivalence of directed pullbacks is separate.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeIdentifications
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TriangleCancellation 𝒯 M ℱ P I E S Q
  using (post-cancel; pre-cancel)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.ComponentNaturality as Natural
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.ComponentTriangles as Triangles

module InverseLaws {C D : CAT} {l : MAP C D} {r : MAP D C}
  (adj : Adjunction l r) where
  private
    module A = Adjunction adj
    module N = Natural.Components 𝒯 M ℱ P I E S adj using (unit-natural; counit-natural)
    module T = Triangles.Components 𝒯 M ℱ P I E S adj using (left-triangle-at; right-triangle-at)

  abstract
    untranspose-transpose : {Γ : CAT} (x : MAP Γ C) (y : MAP Γ D)
      (α : MorphismExpression (l ∘ x) y) →
      ExpressionIso {Γ = Γ} {C = D} {f = l ∘ x} {g = y}
        (A.untranspose x y (A.transpose x y α)) α
    untranspose-transpose {Γ} x y α = post-cancel {Γ = Γ} {C = C} {D = D} l
      {x = x} {y = r ∘ (l ∘ x)} {z = r ∘ y} {w = y}
      (A.unit-at x) (post-expression r α) (A.counit-at y) (A.counit-at (l ∘ x)) α
      (N.counit-natural {Γ = Γ} {x = l ∘ x} {y = y} α) (T.left-triangle-at x)
  
    transpose-untranspose : {Γ : CAT} (x : MAP Γ C) (y : MAP Γ D)
      (β : MorphismExpression x (r ∘ y)) →
      ExpressionIso {Γ = Γ} {C = C} {f = x} {g = r ∘ y}
        (A.transpose x y (A.untranspose x y β)) β
    transpose-untranspose {Γ} x y β = pre-cancel {Γ = Γ} {C = D} {D = C} r
      {x = l ∘ x} {y = l ∘ (r ∘ y)} {z = y} {w = x}
      (post-expression l β) (A.counit-at y) (A.unit-at x) β (A.unit-at (r ∘ y))
      (N.unit-natural {Γ = Γ} {x = x} {y = r ∘ y} β) (T.right-triangle-at y)

```
