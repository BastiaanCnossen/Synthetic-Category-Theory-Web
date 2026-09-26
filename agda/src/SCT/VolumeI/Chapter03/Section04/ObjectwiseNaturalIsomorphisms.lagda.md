# The objectwise criterion for natural isomorphisms

For `prop:Objectwise_Criterion_Natural_Isomorphisms`, encode a natural
transformation as a functor into the arrow category. Its component
condition is a lift of the entire core of the source to the core of
`Iso D`. Fullness lifts the functor itself to `Iso D`. Rezk and diagram
interchange turn this into inverse data for the original transformation.

The condition uses the universal family of objects, rather than only
absolute points. The supplied proof of fullness is discharged by
`FundamentalGroupoids`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter03.Section04.ObjectwiseNaturalIsomorphisms
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I
  using (Ar; NatTrans; identityArrow; Fun; nameFun; decodeFun; name-decodeFun; funPost)
open Rezk 𝒯 M ℱ P I E using (Iso; IsoLift; identityIso; isoArrow; identityIso-arrow)
open Rezk.RezkAxiom R
open import SCT.VolumeI.Chapter03.Section02.FullSubcategories 𝒯 M P using (IsFullSubcategory)
open import SCT.VolumeI.Chapter03.Section02.Factorization.FullSubcategoryFactorization 𝒯 M P using (module Factor)
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.DiagramInterchange 𝒯 M ℱ
  using (module Interchange; nameFun-cong; post-nameFun; decodeFun-cong; decodeFun-post)

module Transformation (C D : CAT) (α : NatTrans C D) where
  module Swap = Interchange [1] C D using (exchange; exchange-isEquiv; exchange-constant)
  arrow = nameFun α

  components : MAP C (Ar D)
  components = decodeFun (Swap.exchange ∘ arrow)

  ComponentsInvertible : Set m
  ComponentsInvertible = FunctorLift (mapPost {C = One} (isoArrow {D})) (mapPost {C = One} components)

  module FromComponents (full : IsFullSubcategory (isoArrow {D})) (inverted : ComponentsInvertible) where
    module Lift = Factor isoArrow full components inverted using (functor; comparison)
    chosen = equiv-lift (rezk-isEquiv D) Lift.functor
    center : MAP C D
    center = FunctorLift.lift chosen

    constant-components : (identityArrow ∘ center) =₁ components
    constant-components = Lift.comparison ∙
      ((isoArrow ◁ FunctorLift.comparison chosen) ∙
        (comp-assoc center identityIso isoArrow ∙ (identityIso-arrow ⁻¹ ▷ center)))

    transposed : (Swap.exchange ∘ (identityArrow ∘ nameFun center)) =₁ (Swap.exchange ∘ arrow)
    transposed = name-decodeFun (Swap.exchange ∘ arrow) ∙
      (nameFun-cong constant-components ∙
        (post-nameFun identityArrow center ∙
          ((Swap.exchange-constant ▷ nameFun center) ∙
            (comp-assoc (nameFun center) identityArrow Swap.exchange) ⁻¹)))

    constant-transformation : (identityArrow ∘ nameFun center) =₁ arrow
    constant-transformation = equiv-reflect Swap.exchange-isEquiv _ _ transposed

    isNaturalIso : IsoLift arrow
    isNaturalIso = record
      { lift = identityIso ∘ nameFun center
      ; comparison = constant-transformation ∙
          ((identityIso-arrow ▷ nameFun center) ∙
            (comp-assoc (nameFun center) identityIso isoArrow) ⁻¹) }
```

Conversely, Rezk presents an invertible transformation as a constant
one. Interchange and decoding then give a lift of its component functor
through `Iso D`. Taking cores gives the required whole family of
invertible components. This direction does not require fullness.

```agda
  module FromNaturalIso (inverted : IsoLift arrow) where
    chosen = equiv-lift (rezk-isEquiv (Fun C D)) (IsoLift.lift inverted)
    center = FunctorLift.lift chosen

    constant-transformation : (identityArrow ∘ center) =₁ arrow
    constant-transformation = IsoLift.comparison inverted ∙
      ((isoArrow ◁ FunctorLift.comparison chosen) ∙
        (comp-assoc center identityIso isoArrow ∙ (identityIso-arrow ⁻¹ ▷ center)))

    transposed : (funPost (identityArrow {D}) ∘ center) =₁ (Swap.exchange ∘ arrow)
    transposed = (Swap.exchange ◁ constant-transformation) ∙
      (comp-assoc center identityArrow Swap.exchange ∙ (Swap.exchange-constant ⁻¹ ▷ center))

    constant-components : (identityArrow ∘ decodeFun center) =₁ components
    constant-components = decodeFun-cong transposed ∙ (decodeFun-post identityArrow center) ⁻¹

    component-lift : MAP C (Iso D)
    component-lift = identityIso ∘ decodeFun center

    component-comparison : (isoArrow ∘ component-lift) =₁ components
    component-comparison = constant-components ∙
      ((identityIso-arrow ▷ decodeFun center) ∙ (comp-assoc (decodeFun center) identityIso isoArrow) ⁻¹)

    components-invertible : ComponentsInvertible
    components-invertible = record
      { lift = mapPost component-lift
      ; comparison = mapPost-cong component-comparison ∙ mapPost-comp component-lift isoArrow }
```
