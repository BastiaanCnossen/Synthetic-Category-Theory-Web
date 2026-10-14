# Realizing operations on families of morphisms

An operation on parameterized morphism expressions that respects
restriction defines a functor between endpoint pullbacks. Its action on
an arbitrary family is obtained by restriction of the universal family.
If two such operations are inverse, their realized functors are inverse.
The endpoint-change law is needed when using the specified base comparison
of a pullback lift.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberOperations
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberLifts 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open Laws.PullbackStructure P

record ExpressionOperation {B C D : CAT} (u v : MAP B C) (s t : MAP B D) : Set (c ⊔ m) where
  field
    apply : {Γ : CAT} (b : MAP Γ B) →
      MorphismExpression (u ∘ b) (v ∘ b) → MorphismExpression (s ∘ b) (t ∘ b)
    on-comparison : {Γ : CAT} (b : MAP Γ B)
      {f g : MorphismExpression (u ∘ b) (v ∘ b)} → ExpressionIso f g →
      ExpressionIso (apply b f) (apply b g)
    on-restriction : {Γ Δ : CAT} (b : MAP Γ B)
      (f : MorphismExpression (u ∘ b) (v ∘ b)) (h : MAP Δ Γ) →
      ExpressionIso (Lifts.restrict s t b (apply b f) h)
        (apply (b ∘ h) (Lifts.restrict u v b f h))
    on-change : {Γ : CAT} {b d : MAP Γ B}
      (f : MorphismExpression (u ∘ b) (v ∘ b)) (σ : b =₁ d) →
      ExpressionIso (retarget-expression (apply b f) (s ◁ σ) (t ◁ σ))
        (apply d (retarget-expression f (u ◁ σ) (v ◁ σ)))

module Realize {B C D : CAT} {u v : MAP B C} {s t : MAP B D}
  (operation : ExpressionOperation u v s t) where
  private
    module O = ExpressionOperation operation
    module Source = Fiber u v using (decode; decode-restrict; read; encode-decode)
    module Target = Lifts s t using (lift-restrict; lift-cong)
  module H = EndpointFiber u v
  module K = EndpointFiber s t

  universal : MorphismExpression (u ∘ H.base) (v ∘ H.base)
  universal = Source.decode (pullbackCone endpoints (pair u v))

  functor : MAP H.category K.category
  functor = K.lift H.base (O.apply H.base universal)

  base : (K.base ∘ functor) =₁ H.base
  base = K.lift-base H.base (O.apply H.base universal)

  abstract
    on-family : {Γ : CAT} (h : MAP Γ H.category) →
      (functor ∘ h) =₁ K.lift (H.base ∘ h) (O.apply (H.base ∘ h) (Source.read h))
    on-family h = Target.lift-cong (H.base ∘ h)
      (expressionIso-compose
        (O.on-comparison (H.base ∘ h) (Source.decode-restrict (pullbackCone endpoints (pair u v)) h))
        (O.on-restriction H.base universal h)) ∙
      Target.lift-restrict H.base (O.apply H.base universal) h

    lift-universal : H.lift H.base universal =₁ id H.category
    lift-universal = Lifts.lift-universal u v

module InverseOperations {B C D : CAT} {u v : MAP B C} {s t : MAP B D}
  (forward : ExpressionOperation u v s t) (backward : ExpressionOperation s t u v)
  (inverse-law : {Γ : CAT} (b : MAP Γ B) (f : MorphismExpression (u ∘ b) (v ∘ b)) →
    ExpressionIso (ExpressionOperation.apply backward b (ExpressionOperation.apply forward b f)) f) where
  private
    module F = ExpressionOperation forward
    module G = ExpressionOperation backward
    module A = Realize forward using (functor; base; universal; lift-universal)
    module Z = Realize backward using (functor; on-family)
    module H = EndpointFiber u v
    module K = EndpointFiber s t
    module Source = Lifts u v using (lift-change)
    module Target = Fiber s t using (read; read-lift)

  abstract
    composite : (Z.functor ∘ A.functor) =₁ id H.category
    composite = A.lift-universal ∙
      Source.lift-change (G.apply (K.base ∘ A.functor) (Target.read A.functor)) A.universal A.base
        (expressionIso-compose (inverse-law H.base A.universal)
          (expressionIso-compose
            (G.on-comparison H.base (Target.read-lift H.base (F.apply H.base A.universal)))
            (G.on-change (Target.read A.functor) A.base))) ∙
      Z.on-family A.functor

module EquivalenceOperations {B C D : CAT} {u v : MAP B C} {s t : MAP B D}
  (forward : ExpressionOperation u v s t) (backward : ExpressionOperation s t u v)
  (left-law : {Γ : CAT} (b : MAP Γ B) (f : MorphismExpression (u ∘ b) (v ∘ b)) →
    ExpressionIso (ExpressionOperation.apply backward b (ExpressionOperation.apply forward b f)) f)
  (right-law : {Γ : CAT} (b : MAP Γ B) (g : MorphismExpression (s ∘ b) (t ∘ b)) →
    ExpressionIso (ExpressionOperation.apply forward b (ExpressionOperation.apply backward b g)) g) where

  isEquiv : IsEquiv (Realize.functor forward)
  isEquiv = record
    { inverse = Realize.functor backward
    ; sectionIso = (InverseOperations.composite forward backward left-law) ⁻¹
    ; retractionIso = (InverseOperations.composite backward forward right-law) ⁻¹ }

  equivalence : Equiv (EndpointFiber.category u v) (EndpointFiber.category s t)
  equivalence = record { functor = Realize.functor forward ; isEquiv = isEquiv }
```
