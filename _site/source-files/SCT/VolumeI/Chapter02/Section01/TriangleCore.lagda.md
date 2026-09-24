# The three points of the triangle core

For `cor:Groupoid_Core_Walking_Commutative_Triangle`, the vertex copairing
is a retract of the four-corner equivalence for the square. The fourth
corner maps to vertex zero. Representing the four corners by a coproduct
makes both retract squares finite point computations. No recognition or
closure axiom for anima coproducts enters the argument.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter02.Section01.IntervalCore as Interval

module SCT.VolumeI.Chapter02.Section01.TriangleCore
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (B : Coproducts.CoproductStructure 𝒯 M)
  (U : Universality.CoproductUniversality 𝒯 M B P)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (K : Interval.IntervalCoreAxiom 𝒯 M B I) where

open import SCT.VolumeI.Chapter02.Section01.FourPoints 𝒯 M B P U
  using (Two; Four; points₄; points₄-post; points₄-cong; module Rectangle;
    _⊔_; in₁; in₂; copair; copair-post; copair-cong; copair-β₁; copair-β₂;
    copair-pre₁; copair-pre₂; copair-η; copair-inclusions; mapPost-name;
    Map; nameMap; nameMapIso; name-decode; mapPost; mapPost-comp; mapPost-cong; mapPost-id;
    mapPre; mapPre-name; oneProduct-in)
open import SCT.VolumeI.Chapter02.Section01.TriangleCorners 𝒯 M ℱ P I E Q
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (Core)
open import SCT.VolumeI.Chapter01.Section04.MappingProducts 𝒯 M using (module ProductComparison)
open import SCT.VolumeI.Chapter01.Section03.Retracts vocabulary terminal products productLaws composition
open Interval 𝒯 M B I using (intervalCore)
open Interval.IntervalCoreAxiom K
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun 𝒯 M ℱ using (module CoreOfFun)

Three : CAT
Three = Two ⊔ One

points₃ : {C : CAT} → Obj-abs C → Obj-abs C → Obj-abs C → MAP Three C
points₃ x y z = copair (copair x y) z

points₃-post : {C D : CAT} (h : MAP C D) (x y z : Obj-abs C) →
  (h ∘ points₃ x y z) =₁ points₃ (h ∘ x) (h ∘ y) (h ∘ z)
points₃-post h x y z = copair-cong (copair-post x y h) (idIso (h ∘ z)) ∙
  copair-post (copair x y) z h

points₃-cong : {C : CAT} {x y z x′ y′ z′ : Obj-abs C} →
  x =₁ x′ → y =₁ y′ → z =₁ z′ → points₃ x y z =₁ points₃ x′ y′ z′
points₃-cong α β γ = copair-cong (copair-cong α β) γ

triangleCore : MAP Three (Core [2])
triangleCore = points₃ (nameMap vertex₀) (nameMap vertex₁) (nameMap vertex₂)

fourCorners : MAP Four (Core ([1] × [1]))
fourCorners = points₄ (nameMap (pair zero zero)) (nameMap (pair one zero))
  (nameMap (pair zero one)) (nameMap (pair one one))

module CoreProduct = ProductComparison One [1] [1] using (forward; forward-isEquiv)
module CoreRectangle = Rectangle (nameMap zero) (nameMap one) (nameMap zero) (nameMap one)
  using (rectangle; isEquiv)

core-pair-point : (x y : Obj-abs [1]) →
  (CoreProduct.forward ∘ nameMap (pair x y)) =₁ pair (nameMap x) (nameMap y)
core-pair-point x y = pair-cong
  (nameMapIso (pair-β₁ x y) ∙ mapPost-name pr₁ (pair x y))
  (nameMapIso (pair-β₂ x y) ∙ mapPost-name pr₂ (pair x y)) ∙
  pair-pre (mapPost pr₁) (mapPost pr₂) (nameMap (pair x y))

fourCorners-isEquiv : IsEquiv fourCorners
fourCorners-isEquiv = equiv-cancel-left fourCorners CoreProduct.forward CoreProduct.forward-isEquiv
  (equiv-transport (comparison ⁻¹) (CoreRectangle.isEquiv intervalCore-isEquiv intervalCore-isEquiv))
  where
  comparison : (CoreProduct.forward ∘ fourCorners) =₁ CoreRectangle.rectangle
  comparison = points₄-cong (core-pair-point zero zero) (core-pair-point one zero)
    (core-pair-point zero one) (core-pair-point one one) ∙
    points₄-post CoreProduct.forward _ _ _ _

t₀ t₁ t₂ : Obj-abs Three
t₀ = in₁ ∘ in₁
t₁ = in₁ ∘ in₂
t₂ = in₂

c₀₀ c₁₀ c₀₁ c₁₁ : Obj-abs Four
c₀₀ = in₁ ∘ in₁
c₁₀ = in₁ ∘ in₂
c₀₁ = in₂ ∘ in₁
c₁₁ = in₂ ∘ in₂

include : MAP Three Four
include = points₃ c₀₀ c₀₁ c₁₁
collapse : MAP Four Three
collapse = points₄ t₀ t₀ t₁ t₂

point₃₀ : {C : CAT} (x y z : Obj-abs C) → (points₃ x y z ∘ t₀) =₁ x
point₃₀ x y z = copair-β₁ x y ∙ copair-pre₁ (copair x y) z in₁
point₃₁ : {C : CAT} (x y z : Obj-abs C) → (points₃ x y z ∘ t₁) =₁ y
point₃₁ x y z = copair-β₂ x y ∙ copair-pre₁ (copair x y) z in₂
point₃₂ : {C : CAT} (x y z : Obj-abs C) → (points₃ x y z ∘ t₂) =₁ z
point₃₂ x y z = copair-β₂ (copair x y) z

point₄₀₀ : {C : CAT} (x y z w : Obj-abs C) → (points₄ x y z w ∘ c₀₀) =₁ x
point₄₀₀ x y z w = copair-β₁ x y ∙ copair-pre₁ (copair x y) (copair z w) in₁
point₄₀₁ : {C : CAT} (x y z w : Obj-abs C) → (points₄ x y z w ∘ c₀₁) =₁ z
point₄₀₁ x y z w = copair-β₁ z w ∙ copair-pre₂ (copair x y) (copair z w) in₁
point₄₁₁ : {C : CAT} (x y z w : Obj-abs C) → (points₄ x y z w ∘ c₁₁) =₁ w
point₄₁₁ x y z w = copair-β₂ z w ∙ copair-pre₂ (copair x y) (copair z w) in₂

collapse-include : (collapse ∘ include) =₁ id Three
collapse-include = copair-inclusions Two One ∙
  (copair-cong (copair-η in₁) (idIso in₂) ∙
    (points₃-cong (point₄₀₀ t₀ t₀ t₁ t₂) (point₄₀₁ t₀ t₀ t₁ t₂) (point₄₁₁ t₀ t₀ t₁ t₂) ∙
      points₃-post collapse c₀₀ c₀₁ c₁₁))

left-square : (fourCorners ∘ include) =₁ (mapPost j₀ ∘ triangleCore)
left-square = (points₃-cong
  (nameMapIso j₀-vertex₀ ∙ mapPost-name j₀ vertex₀)
  (nameMapIso j₀-vertex₁ ∙ mapPost-name j₀ vertex₁)
  (nameMapIso j₀-vertex₂ ∙ mapPost-name j₀ vertex₂) ∙
    points₃-post (mapPost j₀) _ _ _) ⁻¹ ∙
  (points₃-cong (point₄₀₀ _ _ _ _) (point₄₀₁ _ _ _ _) (point₄₁₁ _ _ _ _) ∙
    points₃-post fourCorners c₀₀ c₀₁ c₁₁)

right-square : (triangleCore ∘ collapse) =₁ (mapPost p₀ ∘ fourCorners)
right-square = (points₄-cong
  (nameMapIso p₀-corner₀₀ ∙ mapPost-name p₀ (pair zero zero))
  (nameMapIso p₀-corner₁₀ ∙ mapPost-name p₀ (pair one zero))
  (nameMapIso p₀-corner₀₁ ∙ mapPost-name p₀ (pair zero one))
  (nameMapIso p₀-corner₁₁ ∙ mapPost-name p₀ (pair one one)) ∙
    points₄-post (mapPost p₀) _ _ _ _) ⁻¹ ∙
  (points₄-cong (point₃₀ _ _ _) (point₃₀ _ _ _) (point₃₁ _ _ _) (point₃₂ _ _ _) ∙
    points₄-post triangleCore t₀ t₀ t₁ t₂)

triangleCore-isEquiv : IsEquiv triangleCore
triangleCore-isEquiv = retract-diagram-isEquiv record
  { g = include ; h = collapse ; k = mapPost j₀ ; j = mapPost p₀
  ; leftSquare = left-square ; rightSquare = right-square
  ; α = collapse-include ⁻¹
  ; β = mapPost-id One [2] ∙ (mapPost-cong p₀-j₀ ∙ mapPost-comp j₀ p₀) }
  fourCorners-isEquiv
```

The core of `Fun [1] [1]` is `Map [1] [1]`. The same calculation
therefore identifies the latter anima with the three displayed functors:
the two constants and the identity.

```agda
module Endomorphisms = CoreOfFun [1] [1] using (uncurrying; uncurrying-isEquiv; module U)

uncurry-named-point : (f : MAP [1] [1]) →
  (Endomorphisms.uncurrying ∘ nameMap (nameFun f)) =₁ nameMap f
uncurry-named-point f = nameMapIso (decode-nameFun f) ∙
  (mapPre-name (oneProduct-in [1]) (funUncurry (nameFun f)) ∙
    ((mapPre (oneProduct-in [1]) ◁
      (nameMapIso (Endomorphisms.U.specialize-β (nameFun f)) ∙
        (name-decode (Endomorphisms.U.forward ∘ nameMap (nameFun f))) ⁻¹)) ∙
      comp-assoc (nameMap (nameFun f)) Endomorphisms.U.forward (mapPre (oneProduct-in [1]))))

intervalEndomorphisms : MAP Three (Map [1] [1])
intervalEndomorphisms = points₃ (nameMap (const zero)) (nameMap (id [1])) (nameMap (const one))

intervalEndomorphisms-isEquiv : IsEquiv intervalEndomorphisms
intervalEndomorphisms-isEquiv = equiv-transport
  (points₃-cong (uncurry-named-point (const zero)) (uncurry-named-point (id [1]))
    (uncurry-named-point (const one)) ∙ points₃-post Endomorphisms.uncurrying _ _ _)
  (equiv-compose triangleCore Endomorphisms.uncurrying triangleCore-isEquiv Endomorphisms.uncurrying-isEquiv)
```
