# Covariant and contravariant transport

For `cons:Covariant_Transport`, invert directed evaluation on the
universal family, using its equivalence as a pullback universal property.
The resulting comparison is a comparison of whole endpoint cones.
Projection supplies the starting point and the endpoint in the base.

The last two constructions restrict this family to an absolute morphism
and produce actual functors between the displayed fibers. No objectwise
choice or categorical-context axiom is used.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section02.Transport
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter04.Section02.Lifts 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (module UniversalCone)
open import SCT.VolumeI.Chapter02.Section01.AbsoluteMorphisms 𝒯 M ℱ P I
  using (morphism-expression)

module Covariant {A B : CAT} (f : MAP A B) (e : Fibration.IsLeftFibration f)
  {Γ : CAT} (x : MAP Γ A) (y : MAP Γ B)
  (β : MorphismExpression (f ∘ x) y) where
  open Evaluation f
  input = retarget-expression β (idIso (f ∘ x)) ((comp-unitˡ y) ⁻¹)
  target-cone = Left.cone x y input
  module U = UniversalCone (Left.cone ev₀ (f ∘ ev₁) left-expression) e

  lift : MAP Γ (Ar A)
  lift = U.factor target-cone

  lift-β : ConeIso
    (conePre lift (Left.cone ev₀ (f ∘ ev₁) left-expression)) target-cone
  lift-β = U.factor-β target-cone

  transport : MAP Γ A
  transport = ev₁ ∘ lift

  source-frame : (ev₀ ∘ lift) =₁ x
  source-frame = pair-β₁ x y ∙
    ((pr₁ ◁ ConeIso.rightIso lift-β) ∙ (project-pair₁ ev₀ (f ∘ ev₁) lift) ⁻¹)

  target-frame : (f ∘ transport) =₁ y
  target-frame = pair-β₂ x y ∙
    ((pr₂ ◁ ConeIso.rightIso lift-β) ∙
      ((project-pair₂ ev₀ (f ∘ ev₁) lift) ⁻¹ ∙ (comp-assoc lift ev₁ f) ⁻¹))

  image : (funPost f ∘ lift) =₁ (MorphismExpression.arrow β)
  image = ConeIso.leftIso lift-β

  lifted-expression : MorphismExpression x transport
  lifted-expression = record
    { arrow = lift ; source-frame = source-frame ; target-frame = idIso transport }

module Contravariant {A B : CAT} (f : MAP A B) (e : Fibration.IsRightFibration f)
  {Γ : CAT} (x : MAP Γ B) (y : MAP Γ A)
  (β : MorphismExpression x (f ∘ y)) where
  open Evaluation f
  input = retarget-expression β ((comp-unitˡ x) ⁻¹) (idIso (f ∘ y))
  target-cone = Right.cone x y input
  module U = UniversalCone (Right.cone (f ∘ ev₀) ev₁ right-expression) e

  lift : MAP Γ (Ar A)
  lift = U.factor target-cone

  lift-β : ConeIso
    (conePre lift (Right.cone (f ∘ ev₀) ev₁ right-expression)) target-cone
  lift-β = U.factor-β target-cone

  transport : MAP Γ A
  transport = ev₀ ∘ lift

  source-frame : (f ∘ transport) =₁ x
  source-frame = pair-β₁ x y ∙
    ((pr₁ ◁ ConeIso.rightIso lift-β) ∙
      ((project-pair₁ (f ∘ ev₀) ev₁ lift) ⁻¹ ∙ (comp-assoc lift ev₀ f) ⁻¹))

  target-frame : (ev₁ ∘ lift) =₁ y
  target-frame = pair-β₂ x y ∙
    ((pr₂ ◁ ConeIso.rightIso lift-β) ∙ (project-pair₂ (f ∘ ev₀) ev₁ lift) ⁻¹)

  image : (funPost f ∘ lift) =₁ (MorphismExpression.arrow β)
  image = ConeIso.leftIso lift-β

  lifted-expression : MorphismExpression transport y
  lifted-expression = record
    { arrow = lift ; source-frame = idIso transport ; target-frame = target-frame }

module CovariantFiber {A B : CAT} (f : MAP A B) (e : Fibration.IsLeftFibration f)
  {x y : Obj-abs B} (β : Morphism x y) where
  source-fiber = Pullback f x
  target-fiber = Pullback f y
  object = pullback₁ {f = f} {x}
  parameter = pullback₂ {f = f} {x}
  absolute = retarget-expression (morphism-expression β) (const-One x) (const-One y)
  family = retarget-expression (restrict-expression absolute parameter)
    (pullbackMatch ⁻¹) (idIso (y ∘ parameter))
  module Lift = Covariant f e object (y ∘ parameter) family

  transport-cone : Cone f y source-fiber
  transport-cone = record
    { left = Lift.transport ; right = parameter ; match = Lift.target-frame }

  transport : MAP source-fiber target-fiber
  transport = pullbackLift transport-cone

  transport-β : ConeIso (conePre transport (pullbackCone f y)) transport-cone
  transport-β = pullbackLift-β transport-cone

module ContravariantFiber {A B : CAT} (f : MAP A B) (e : Fibration.IsRightFibration f)
  {x y : Obj-abs B} (β : Morphism x y) where
  source-fiber = Pullback f y
  target-fiber = Pullback f x
  object = pullback₁ {f = f} {y}
  parameter = pullback₂ {f = f} {y}
  absolute = retarget-expression (morphism-expression β) (const-One x) (const-One y)
  family = retarget-expression (restrict-expression absolute parameter)
    (idIso (x ∘ parameter)) (pullbackMatch ⁻¹)
  module Lift = Contravariant f e (x ∘ parameter) object family

  transport-cone : Cone f x source-fiber
  transport-cone = record
    { left = Lift.transport ; right = parameter ; match = Lift.source-frame }

  transport : MAP source-fiber target-fiber
  transport = pullbackLift transport-cone

  transport-β : ConeIso (conePre transport (pullbackCone f x)) transport-cone
  transport-β = pullbackLift-β transport-cone
```

