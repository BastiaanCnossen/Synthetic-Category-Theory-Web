# The induced square of functor categories

Precomposition supplies the four functors in
`prop:Mapping_Out_Of_Pushouts`. We choose its matching by lifting the
explicit evaluated comparison, so its uncurrying witness remains available.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section08.FunctorSquares
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.IsomorphismLifting 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.Squares 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P

preCompRaw : {A B C E : CAT} (f : MAP A B) (g : MAP B C) →
  (funUncurry (funPre {D = E} f ∘ funPre g)) =₁ (funUncurry (funPre (g ∘ f)))
preCompRaw {C = C} {E} f g = (funPre-β (g ∘ f)) ⁻¹ ∙
  ((funEval ◁ (productMap-cong (comp-unitˡ (id (Fun C E))) (idIso (g ∘ f)) ∙
     productMap-comp (id (Fun C E)) (id (Fun C E)) f g)) ∙
  (comp-assoc (productMap (id (Fun C E)) f) (productMap (id (Fun C E)) g) funEval ∙
  ((funPre-β g ▷ productMap (id (Fun C E)) f) ∙ funPre-uncurry f (funPre g))))

preCongRaw : {B C E : CAT} {f g : MAP B C} (α : f =₁ g) →
  (funUncurry (funPre {D = E} f)) =₁ (funUncurry (funPre g))
preCongRaw {C = C} {E} {f} {g} α = (funPre-β g) ⁻¹ ∙
  ((funEval ◁ productMap-cong (idIso (id (Fun C E))) α) ∙ funPre-β f)

preComp : {A B C E : CAT} (f : MAP A B) (g : MAP B C) →
  (funPre {D = E} f ∘ funPre g) =₁ (funPre (g ∘ f))
preComp f g = funIsoReflect _ _ (preCompRaw f g)

preCong : {B C E : CAT} {f g : MAP B C} → f =₁ g →
  (funPre {D = E} f) =₁ (funPre g)
preCong α = funIsoReflect _ _ (preCongRaw α)

preComp-β : {A B C E : CAT} (f : MAP A B) (g : MAP B C) →
  (funUncurryIso (preComp {E = E} f g)) =₂ (preCompRaw f g)
preComp-β f g = funIsoReflect-β _ _ (preCompRaw f g)

preCong-β : {B C E : CAT} {f g : MAP B C} (α : f =₁ g) →
  (funUncurryIso (preCong {E = E} α)) =₂ (preCongRaw α)
preCong-β α = funIsoReflect-β _ _ (preCongRaw α)

module Induced {A B C D : CAT}
  {u : MAP A B} {l : MAP A C} {r : MAP B D} {v : MAP C D}
  (s : Square u l r v) (E : CAT) where

  rawMatching : (funUncurry (funPre {D = E} u ∘ funPre r)) =₁
    (funUncurry (funPre l ∘ funPre v))
  rawMatching = (preCompRaw l v) ⁻¹ ∙
    (preCongRaw (Square.commute s) ∙ preCompRaw u r)

  value : Cone (funPre {D = E} u) (funPre l) (Fun D E)
  value = record { left = funPre r ; right = funPre v
    ; match = (preComp l v) ⁻¹ ∙ (preCong (Square.commute s) ∙ preComp u r) }

  matching-β : (funUncurryIso (Cone.match value)) =₂ rawMatching
  matching-β = isoComp-cong (＝-inv ◁ preComp-β l v)
      (isoComp-cong (preCong-β (Square.commute s)) (preComp-β u r)) ∙
    (isoComp-cong (funUncurryIso-inverse (preComp l v))
      (funUncurryIso-comp (preCong (Square.commute s)) (preComp u r)) ∙
      funUncurryIso-comp ((preComp l v) ⁻¹) (preCong (Square.commute s) ∙ preComp u r))

functorOut : {A B C D : CAT}
  {u : MAP A B} {l : MAP A C} {r : MAP B D} {v : MAP C D} →
  Square u l r v → (E : CAT) → Cone (funPre {D = E} u) (funPre l) (Fun D E)
functorOut = Induced.value

FunctorCriterion : {A B C D : CAT}
  {u : MAP A B} {l : MAP A C} {r : MAP B D} {v : MAP C D} →
  Square u l r v → Set (c ⊔ m)
FunctorCriterion s = (E : CAT) → IsPullback (functorOut s E)
```
