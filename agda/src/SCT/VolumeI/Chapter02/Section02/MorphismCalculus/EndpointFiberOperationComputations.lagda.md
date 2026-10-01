# Computing a realized operation on a family

The computation of a realized morphism operation holds as a comparison
of complete endpoint cones. Restrict its defining cone, apply the
operation's restriction law, and decode the restricted input. This
retains the base comparison needed when the result is used in a square.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberOperationComputations
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberOperations 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open Laws.PullbackStructure P using (pullbackCone)

module Of {B C D : CAT} {u v : MAP B C} {s t : MAP B D}
  (operation : ExpressionOperation u v s t) where
  private
    module O = ExpressionOperation operation
      using (apply; on-change; on-comparison; on-restriction)
    module R = Realize operation using (functor; universal)
    module H = EndpointFiber u v
      using (base; category; cone)
    module K = EndpointFiber s t
      using (cone; lift-β)
    module Source = Fiber u v using (read; decode-restrict; read-lift; decode-comparison; decode-encode)
    module Target = Lifts s t using (restrict; encode-restrict; encode-cong)
    module Input = Lifts u v using (restrict)

  module At {Γ : CAT} (h : MAP Γ H.category) where
    base : MAP Γ B
    base = H.base ∘ h
    family : MorphismExpression (s ∘ base) (t ∘ base)
    family = O.apply base (Source.read h)
    cone : Cone endpoints (pair s t) Γ
    cone = K.cone base family
    private
      output : MorphismExpression (s ∘ H.base) (t ∘ H.base)
      output = O.apply H.base R.universal
      restricted : MorphismExpression (s ∘ base) (t ∘ base)
      restricted = Target.restrict H.base output h
      intermediate : MorphismExpression (s ∘ base) (t ∘ base)
      intermediate = O.apply base (Input.restrict H.base R.universal h)
      abstract
        expression-computation : ExpressionIso restricted family
        expression-computation = expressionIso-compose
          (O.on-comparison base
            (Source.decode-restrict (pullbackCone endpoints (pair u v)) h))
          (O.on-restriction H.base R.universal h)

    abstract
      computation : ConeIso
        (conePre (R.functor ∘ h) (pullbackCone endpoints (pair s t))) cone
      computation = coneIso-compose
        (Target.encode-cong base {f = restricted} {g = family} expression-computation)
        (coneIso-compose (Target.encode-restrict H.base output h)
          (coneIso-compose (coneIso-pre h (K.lift-β H.base output))
            (coneIso-inverse (conePre-assoc h R.functor (pullbackCone endpoints (pair s t))))))


  module Specified {Γ : CAT} (h : MAP Γ H.category) (b : MAP Γ B)
    (f : MorphismExpression (u ∘ b) (v ∘ b))
    (Φ : ConeIso (conePre h (pullbackCone endpoints (pair u v))) (H.cone b f)) where
    private
      module InputFamily = At h using (base; family; computation)
      module Output = Fiber s t using (encode-comparison)
      σ : InputFamily.base =₁ b
      σ = ConeIso.rightIso Φ
      abstract
        input-comparison : ExpressionIso
          (retarget-expression (Source.read h) (u ◁ σ) (v ◁ σ)) f
        input-comparison = expressionIso-compose (Source.decode-encode b f)
          (Source.decode-comparison Φ)
        output-comparison : ExpressionIso
          (retarget-expression InputFamily.family (s ◁ σ) (t ◁ σ)) (O.apply b f)
        output-comparison = expressionIso-compose (O.on-comparison b input-comparison)
          (O.on-change (Source.read h) σ)

    cone : Cone endpoints (pair s t) Γ
    cone = K.cone b (O.apply b f)
    abstract
      computation : ConeIso
        (conePre (R.functor ∘ h) (pullbackCone endpoints (pair s t))) cone
      computation = coneIso-compose
        (Output.encode-comparison InputFamily.base b InputFamily.family (O.apply b f) σ output-comparison)
        InputFamily.computation
```
