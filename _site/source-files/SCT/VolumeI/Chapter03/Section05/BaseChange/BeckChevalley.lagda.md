# The Beck–Chevalley comparison

For `cons:Beck-Chevalley_Exponentiability`, pull the evaluation functor
across the specified square and then relatively curry it. The
construction actually works for any commutative square. Exponentiability
will require it to be an equivalence for the pullback squares in the
definition.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.BaseChange.BeckChevalley
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.Currying.RelativeTransposition 𝒯 M ℱ P using (module Transpose)
open import SCT.VolumeI.Chapter03.Section05.DependentProductUniqueness 𝒯 M ℱ P using (module Uniqueness)

module BeckChevalley {S T S′ T′ C : CAT} (p : MAP S T) (b : MAP T′ T)
  (square : Cone p b S′) (f : MAP C S)
  (Π : DependentProduct p f)
  (Π′ : DependentProduct (Cone.right square) (pullback₂ {f = f} {Cone.left square})) where

  h = Cone.left square
  p′ = Cone.right square
  D = DependentProduct.category Π
  g = DependentProduct.projection Π
  ε = DependentProduct.evaluation Π
  D′ = DependentProduct.category Π′
  g′ = DependentProduct.projection Π′
  E = Pullback g b
  t : MAP E T′
  t = pullback₂
  source = Pullback t p′
  target = Pullback f h
  target-projection : MAP target S′
  target-projection = pullback₂

  evaluation-domain-cone : Cone g p source
  evaluation-domain-cone = record
    { left = pullback₁ {f = g} {b} ∘ pullback₁ {f = t} {p′}
    ; right = h ∘ pullback₂ {f = t} {p′}
    ; match = comp-assoc pullback₂ h p ∙
        ((Cone.match square ⁻¹ ▷ pullback₂) ∙
          ((comp-assoc pullback₂ p′ b) ⁻¹ ∙
            ((b ◁ pullbackMatch {f = t} {p′}) ∙
              (comp-assoc pullback₁ t b ∙
                ((pullbackMatch {f = g} {b} ▷ pullback₁) ∙
                  (comp-assoc pullback₁ (pullback₁ {f = g} {b}) g) ⁻¹))))) }

  into-evaluation : MAP source (Pullback g p)
  into-evaluation = pullbackLift evaluation-domain-cone

  pulled-evaluation-cone : Cone f h source
  pulled-evaluation-cone = record
    { left = FunctorLift.lift ε ∘ into-evaluation
    ; right = pullback₂ {f = t} {p′}
    ; match = pullbackLift-β₂ evaluation-domain-cone ∙
        ((FunctorLift.comparison ε ▷ into-evaluation) ∙
          (comp-assoc into-evaluation (FunctorLift.lift ε) f) ⁻¹) }

  pulled-evaluation : FunctorOver (pullback₂ {f = t} {p′}) target-projection
  pulled-evaluation = record
    { lift = pullbackLift pulled-evaluation-cone
    ; comparison = pullbackLift-β₂ pulled-evaluation-cone }

  module Curry = RelativeCurrying.At p′ target-projection Π′ t
    using (curry; uncurry; uncurry-curry)

  uncurried-point : Obj-abs (MapOver (pullback₂ {f = t} {p′}) target-projection)
  uncurried-point = Over.name-over (pullback₂ {f = t} {p′}) target-projection pulled-evaluation

  module Transposed = Transpose p′ target-projection Π′ t pulled-evaluation

  abstract
    point : Obj-abs (MapOver t g′)
    point = Transposed.point

    over : FunctorOver t g′
    over = Transposed.over

    functor : MAP E D′
    functor = FunctorLift.lift over

    triangle : (g′ ∘ functor) =₁ t
    triangle = FunctorLift.comparison over

    uncurrying-comparison : (Curry.uncurry ∘ point) =₁ uncurried-point
    uncurrying-comparison = Transposed.uncurrying-comparison

    decoded-uncurrying-comparison :
      (Curry.uncurry ∘ Over.name-over t g′ over) =₁ uncurried-point
    decoded-uncurrying-comparison = Transposed.comparison
    from-pulled-universal-property : IsDependentProduct p′ target-projection t pulled-evaluation →
      IsEquiv functor
    from-pulled-universal-property universal = Uniqueness.forward-isEquiv p′ target-projection
      (record { category = E ; projection = t ; evaluation = pulled-evaluation
              ; isDependentProduct = universal }) Π′


```

The raw comparison into the evaluation domain is a pullback lift, with
its whole cone comparison supplied by `pullbackLift-β`. The final
uncurrying comparison takes place in the relative mapping anima, so it
retains the triangle over the new base.

If the pulled evaluation itself satisfies the dependent-product universal
property, uniqueness proves that this actual Beck–Chevalley functor is
an equivalence. The comparison is definitionally the same transposition
as the forward functor in the uniqueness theorem.
