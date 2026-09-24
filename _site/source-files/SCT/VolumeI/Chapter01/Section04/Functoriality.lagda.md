# Functoriality of mapping animae

Postcomposition and precomposition are obtained by currying evaluation.
Their formulas on an arbitrary anima of parameters are proved before the
composition laws. In this way the composition laws compare actual functors
between mapping animae, rather than just their absolute points.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Currying as Currying

module SCT.VolumeI.Chapter01.Section04.Functoriality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open Currying 𝒯 M

mapPost : {C D E : CAT} → MAP D E → MAP (Map C D) (Map C E)
mapPost {C} {D} g = mapCurry (map-isAn C D) (g ∘ mapEval)

mapPre : {B C D : CAT} → MAP B C → MAP (Map C D) (Map B D)
mapPre {C = C} {D} f = mapCurry (map-isAn C D)
  (mapEval ∘ productMap (id (Map C D)) f)

mapPost-β : {C D E : CAT} (g : MAP D E)
  → (mapUncurry (mapPost {C = C} g)) =₁ (g ∘ mapEval)
mapPost-β {C} {D} g = mapCurry-β (map-isAn C D) (g ∘ mapEval)

mapPre-β : {B C D : CAT} (f : MAP B C)
  → (mapUncurry (mapPre {D = D} f)) =₁
      (mapEval ∘ productMap (id (Map C D)) f)
mapPre-β {C = C} {D} f = mapCurry-β (map-isAn C D)
  (mapEval ∘ productMap (id (Map C D)) f)

mapPost-cong : {C D E : CAT} {g g′ : MAP D E}
  → g =₁ g′ → (mapPost {C = C} g) =₁ (mapPost g′)
mapPost-cong {C} {D} {g = g} {g′} γ =
  mapReflect (map-isAn C D) (mapPost g) (mapPost g′)
    ((mapPost-β g′) ⁻¹ ∙ ((γ ▷ mapEval) ∙ mapPost-β g))

mapPre-cong : {B C D : CAT} {f f′ : MAP B C}
  → f =₁ f′ → (mapPre {D = D} f) =₁ (mapPre f′)
mapPre-cong {C = C} {D} {f} {f′} φ =
  mapReflect (map-isAn C D) (mapPre f) (mapPre f′)
    ((mapPre-β f′) ⁻¹ ∙
      ((mapEval ◁ productMap-cong (idIso (id (Map C D))) φ) ∙ mapPre-β f))

mapPost-uncurry : {X C D E : CAT} (g : MAP D E) (h : MAP X (Map C D))
  → (mapUncurry (mapPost g ∘ h)) =₁ (g ∘ mapUncurry h)
mapPost-uncurry {C = C} g h =
  comp-assoc (productMap h (id C)) mapEval g ∙
    ((mapPost-β g ▷ productMap h (id C)) ∙ mapUncurry-restrict (mapPost g) h)
```

For precomposition the two product maps act in different coordinates.
The following comparison retains both product composition comparisons and
the four unitors used to put them in the same form.

```agda
productMap-separate : {A B C D : CAT} (f : MAP A C) (g : MAP B D)
  → (productMap (id C) g ∘ productMap f (id B)) =₁
      (productMap f (id D) ∘ productMap (id A) g)
productMap-separate {A} {B} {C} {D} f g =
  (productMap-comp (id A) f g (id D)) ⁻¹ ∙
  ((productMap-cong (comp-unitʳ f) (comp-unitˡ g)) ⁻¹ ∙
  (productMap-cong (comp-unitˡ f) (comp-unitʳ g) ∙
   productMap-comp f (id C) (id B) g))

mapPre-uncurry : {X B C D : CAT} (f : MAP B C) (h : MAP X (Map C D))
  → (mapUncurry (mapPre f ∘ h)) =₁
      (mapUncurry h ∘ productMap (id X) f)
mapPre-uncurry {X} {B} {C} {D} f h =
  (comp-assoc (productMap (id X) f) (productMap h (id C)) mapEval) ⁻¹ ∙
  ((mapEval ◁ productMap-separate h f) ∙
  (comp-assoc (productMap h (id B)) (productMap (id (Map C D)) f) mapEval ∙
  ((mapPre-β f ▷ productMap h (id B)) ∙ mapUncurry-restrict (mapPre f) h)))
```

The identity and composition laws now follow by uncurrying and lifting.
All lifting parameters below are mapping animae, as required by the axiom.

```agda
mapPost-id : (C D : CAT) → (mapPost {C = C} (id D)) =₁ (id (Map C D))
mapPost-id C D = mapReflect (map-isAn C D) _ _
  ((mapUncurry-id C D) ⁻¹ ∙ (comp-unitˡ mapEval ∙ mapPost-β (id D)))

mapPre-id : (C D : CAT) → (mapPre {D = D} (id C)) =₁ (id (Map C D))
mapPre-id C D = mapReflect (map-isAn C D) _ _
  ((mapUncurry-id C D) ⁻¹ ∙
    (comp-unitʳ mapEval ∙ ((mapEval ◁ productMap-id (Map C D) C) ∙ mapPre-β (id C))))

mapPost-comp : {A B C D : CAT} (f : MAP B C) (g : MAP C D)
  → (mapPost {C = A} g ∘ mapPost f) =₁ (mapPost (g ∘ f))
mapPost-comp {A} {B} f g = mapReflect (map-isAn A B) _ _
  ((mapPost-β (g ∘ f)) ⁻¹ ∙
  ((comp-assoc mapEval f g) ⁻¹ ∙
  ((g ◁ mapPost-β f) ∙ mapPost-uncurry g (mapPost f))))

mapPre-comp : {A B C D : CAT} (f : MAP A B) (g : MAP B C)
  → (mapPre {D = D} f ∘ mapPre g) =₁ (mapPre (g ∘ f))
mapPre-comp {C = C} {D} f g = mapReflect (map-isAn C D) _ _
  ((mapPre-β (g ∘ f)) ⁻¹ ∙
  ((mapEval ◁ (productMap-cong (comp-unitˡ (id (Map C D))) (idIso (g ∘ f)) ∙
     productMap-comp (id (Map C D)) (id (Map C D)) f g)) ∙
  (comp-assoc (productMap (id (Map C D)) f) (productMap (id (Map C D)) g) mapEval ∙
  ((mapPre-β g ▷ productMap (id (Map C D)) f) ∙ mapPre-uncurry f (mapPre g)))))
```

An inverse functor induces an inverse on mapping animae. The inverse
comparisons use the composition and identity comparisons just proved.

```agda
mapPost-isEquiv : {A C D : CAT} (f : MAP C D) → IsEquiv f
  → IsEquiv (mapPost {C = A} f)
mapPost-isEquiv {A} {C} {D} f e = record
  { inverse = mapPost (IsEquiv.inverse e)
  ; sectionIso = (mapPost-comp f (IsEquiv.inverse e)) ⁻¹ ∙
      (mapPost-cong (IsEquiv.sectionIso e) ∙ (mapPost-id A C) ⁻¹)
  ; retractionIso = (mapPost-comp (IsEquiv.inverse e) f) ⁻¹ ∙
      (mapPost-cong (IsEquiv.retractionIso e) ∙ (mapPost-id A D) ⁻¹)
  }

mapPre-isEquiv : {C D E : CAT} (f : MAP C D) → IsEquiv f
  → IsEquiv (mapPre {D = E} f)
mapPre-isEquiv {C} {D} {E} f e = record
  { inverse = mapPre (IsEquiv.inverse e)
  ; sectionIso = (mapPre-comp (IsEquiv.inverse e) f) ⁻¹ ∙
      (mapPre-cong (IsEquiv.retractionIso e) ∙ (mapPre-id D E) ⁻¹)
  ; retractionIso = (mapPre-comp f (IsEquiv.inverse e)) ⁻¹ ∙
      (mapPre-cong (IsEquiv.sectionIso e) ∙ (mapPre-id C E) ⁻¹)
  }
```
