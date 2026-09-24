# Naming diagrams and their comparisons

Naming and restriction retain their specified uncurrying images. These
computation rules allow subsequent proofs to transport vertex equations.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter02.Section02.DiagramNames
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EndpointNaturality 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section07.IsomorphismLifting 𝒯 M ℱ
import SCT.VolumeI.Chapter01.Section03.Structural as Structural
open Structural vocabulary terminal products productLaws composition whiskering
  using (preWhisker-comp-at)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

name-cong-raw : {A C : CAT} {f g : MAP A C} → f =₁ g →
  (funUncurry (nameFun f)) =₁ (funUncurry (nameFun g))
name-cong-raw {f = f} {g} α = (funCurry-β (g ∘ pr₂)) ⁻¹ ∙
  ((α ▷ pr₂) ∙ funCurry-β (f ∘ pr₂))

name-cong : {A C : CAT} {f g : MAP A C} → f =₁ g → (nameFun f) =₁ (nameFun g)
name-cong α = funIsoReflect _ _ (name-cong-raw α)

name-cong-β : {A C : CAT} {f g : MAP A C} (α : f =₁ g) →
  (funUncurryIso (name-cong α)) =₂ (name-cong-raw α)
name-cong-β α = funIsoReflect-β _ _ (name-cong-raw α)

named-restriction-raw : {A B C : CAT} (r : MAP A B) (f : MAP B C) →
  (funUncurry (funPre r ∘ nameFun f)) =₁ (funUncurry (nameFun (f ∘ r)))
named-restriction-raw r f =
  (funCurry-β ((f ∘ r) ∘ pr₂)) ⁻¹ ∙
    ((comp-assoc pr₂ r f) ⁻¹ ∙
    ((f ◁ pair-β₂ (id One ∘ pr₁) (r ∘ pr₂)) ∙
    (comp-assoc (productMap (id One) r) pr₂ f ∙
      ((funCurry-β (f ∘ pr₂) ▷ productMap (id One) r) ∙
        funPre-uncurry r (nameFun f)))))

named-restriction : {A B C : CAT} (r : MAP A B) (f : MAP B C) →
  (funPre r ∘ nameFun f) =₁ (nameFun (f ∘ r))
named-restriction r f = funIsoReflect _ _ (named-restriction-raw r f)

named-restriction-β : {A B C : CAT} (r : MAP A B) (f : MAP B C) →
  (funUncurryIso (named-restriction r f)) =₂ (named-restriction-raw r f)
named-restriction-β r f = funIsoReflect-β _ _ (named-restriction-raw r f)
```

Evaluation of a named diagram is natural in its identification. The
proof first uses the prescribed image of `name-cong`, then the naturality
of evaluation, and finally the product projection and terminal comparisons.

```agda
module NameNaturality {A C : CAT} (x : Obj-abs A) {f g : MAP A C} (α : f =₁ g) where
  nf = nameFun f
  ng = nameFun g
  δ = name-cong α
  βf : (funUncurry nf) =₁ (f ∘ pr₂ {One} {A})
  βf = funCurry-β (f ∘ pr₂)
  βg : (funUncurry ng) =₁ (g ∘ pr₂ {One} {A})
  βg = funCurry-β (g ∘ pr₂)
  i = insert {X = One} x
  projection = pair-β₂ (id One) (const x)
  terminal-comparison = const-One x

  raw-square : (βg ∙ funUncurryIso δ) =₂ ((α ▷ pr₂) ∙ βf)
  raw-square = cancel-inverse βg ((α ▷ pr₂) ∙ βf) ∙
    isoComp-cong (idIso βg) (name-cong-β α)

  restricted-square : ((βg ▷ i) ∙ (funUncurryIso δ ▷ i)) =₂
    (((α ▷ pr₂) ▷ i) ∙ (βf ▷ i))
  restricted-square = preWhisker-isoComp-at (α ▷ pr₂) βf i ∙
    ((preWhisker i ◁ raw-square) ∙ (preWhisker-isoComp-at βg (funUncurryIso δ) i) ⁻¹)

  curried-square : (evaluate-curry x (g ∘ pr₂) ∙ (evaluate x ◁ δ)) =₂
    (((α ▷ pr₂) ▷ i) ∙ evaluate-curry x (f ∘ pr₂))
  curried-square = paste-squares (evaluate-uncurry x nf) (evaluate-uncurry x ng)
    (βf ▷ i) (βg ▷ i) (evaluate x ◁ δ) (funUncurryIso δ ▷ i) ((α ▷ pr₂) ▷ i)
    (Evaluation.natural x δ) restricted-square

  associated-square :
    ((comp-assoc i pr₂ g ∙ evaluate-curry x (g ∘ pr₂)) ∙ (evaluate x ◁ δ)) =₂
    ((α ▷ (pr₂ ∘ i)) ∙ (comp-assoc i pr₂ f ∙ evaluate-curry x (f ∘ pr₂)))
  associated-square = paste-squares (evaluate-curry x (f ∘ pr₂)) (evaluate-curry x (g ∘ pr₂))
    (comp-assoc i pr₂ f) (comp-assoc i pr₂ g) (evaluate x ◁ δ) ((α ▷ pr₂) ▷ i) (α ▷ (pr₂ ∘ i))
    curried-square (preWhisker-comp-at α pr₂ i)

  projected-square :
    (((g ◁ projection) ∙ (comp-assoc i pr₂ g ∙ evaluate-curry x (g ∘ pr₂))) ∙ (evaluate x ◁ δ)) =₂
    ((α ▷ const x) ∙ ((f ◁ projection) ∙ (comp-assoc i pr₂ f ∙ evaluate-curry x (f ∘ pr₂))))
  projected-square = paste-squares
    (comp-assoc i pr₂ f ∙ evaluate-curry x (f ∘ pr₂)) (comp-assoc i pr₂ g ∙ evaluate-curry x (g ∘ pr₂))
    (f ◁ projection) (g ◁ projection) (evaluate x ◁ δ) (α ▷ (pr₂ ∘ i)) (α ▷ const x)
    associated-square ((interchange-at α projection) ⁻¹)

  natural : (evaluate-name x g ∙ (evaluate x ◁ name-cong α)) =₂
    ((α ▷ x) ∙ evaluate-name x f)
  natural = paste-squares
    ((f ◁ projection) ∙ (comp-assoc i pr₂ f ∙ evaluate-curry x (f ∘ pr₂)))
    ((g ◁ projection) ∙ (comp-assoc i pr₂ g ∙ evaluate-curry x (g ∘ pr₂)))
    (f ◁ terminal-comparison) (g ◁ terminal-comparison) (evaluate x ◁ δ) (α ▷ const x) (α ▷ x)
    projected-square ((interchange-at α terminal-comparison) ⁻¹)
```
