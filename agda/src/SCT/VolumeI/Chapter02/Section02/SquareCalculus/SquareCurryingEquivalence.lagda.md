# The equivalence supplied by coherent square currying

The double-currying construction used for the boundary and corner
calculations is an equivalence. Compare its double evaluation with the
exponential equivalence after swapping the two diagram coordinates.
This comparison concerns the underlying functors; subsequent boundary
calculations continue to use the specified witnesses of `SquareCurrying`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section07.ExponentialLaw as Exponentials
import SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareCurrying as Currying

module SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareCurryingEquivalence
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ public

module Family {Γ A B C : CAT} (W : MAP Γ (Fun (A × B) C)) where
  Flat = Fun (A × B) C
  Nested = Fun B (Fun A C)
  module Curried = Currying.At 𝒯 M ℱ W
  module Exp = Exponentials.ExponentialLaw 𝒯 M ℱ B A C
  module Assoc = Associativity Γ B A

  forward : MAP Γ Nested
  forward = Curried.nested

  swap-diagrams : MAP Flat (Fun (B × A) C)
  swap-diagrams = funPre swap

  private
    k : MAP ((Γ × B) × A) (Γ × (B × A))
    k = Assoc.forward
    shape : MAP ((Γ × B) × A) (B × A)
    shape = pair (pr₂ ∘ pr₁) pr₂
    change : MAP (Γ × (B × A)) (Γ × (A × B))
    change = productMap (id Γ) (swap {B} {A})
    parameter : ((id Γ ∘ pr₁) ∘ k) =₁ (pr₁ ∘ pr₁)
    parameter = pair-β₁ (pr₁ ∘ pr₁) shape ∙ (comp-unitˡ pr₁ ▷ k)
    rectangle : ((swap ∘ pr₂) ∘ k) =₁ (pair pr₂ (pr₂ ∘ pr₁))
    rectangle = pair-cong (pair-β₂ (pr₂ ∘ pr₁) pr₂) (pair-β₁ (pr₂ ∘ pr₁) pr₂) ∙
      pair-pre pr₂ pr₁ shape ∙ (swap ◁ pair-β₂ (pr₁ ∘ pr₁) shape) ∙
      comp-assoc k pr₂ swap

  coordinates : (change ∘ k) =₁ Curried.Coordinates.permute
  coordinates = pair-cong parameter rectangle ∙ pair-pre (id Γ ∘ pr₁) (swap ∘ pr₂) k

  abstract
    curried-evaluation : Exp.doubleUncurry forward =₁ Curried.diagram
    curried-evaluation = funCurry-β Curried.diagram ∙ funUncurry-cong (funCurry-β Curried.first-curry)

    exponential-evaluation : Exp.doubleUncurry (Exp.backward ∘ (swap-diagrams ∘ W)) =₁ Curried.diagram
    exponential-evaluation = (funUncurry W ◁ coordinates) ∙ comp-assoc k change (funUncurry W) ∙
      (funPre-uncurry swap W ▷ k) ∙ Exp.backward-represents (swap-diagrams ∘ W)

    comparison : forward =₁ (Exp.backward ∘ (swap-diagrams ∘ W))
    comparison = Exp.doubleReflect forward (Exp.backward ∘ (swap-diagrams ∘ W))
      (exponential-evaluation ⁻¹ ∙ curried-evaluation)

  backward-isEquiv : IsEquiv Exp.backward
  backward-isEquiv = equiv-cancel-left Exp.backward Exp.forward Exp.forward-isEquiv
    (equiv-transport (Exp.forward-backward ⁻¹) (id-isEquiv (Fun (B × A) C)))

  isEquiv : IsEquiv W → IsEquiv forward
  isEquiv e = equiv-transport (comparison ⁻¹)
    (equiv-compose (swap-diagrams ∘ W) Exp.backward
      (equiv-compose W swap-diagrams e (funPre-isEquiv swap (swap-isEquiv B A))) backward-isEquiv)

module At (A B C : CAT) where
  module Universal = Family (id (Fun (A × B) C))
  open Universal public using (forward; module Curried)
  isEquiv : IsEquiv forward
  isEquiv = Universal.isEquiv (id-isEquiv (Fun (A × B) C))
```
