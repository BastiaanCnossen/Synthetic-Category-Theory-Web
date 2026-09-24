# Functoriality of functor categories

Postcomposition and precomposition are obtained by currying evaluation.
Their formulas on an arbitrary category of parameters are proved before the
composition laws. In this way the composition laws compare actual functors
between functor categories, rather than just their absolute points.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.Currying as Currying

import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.Functoriality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) (F : Categories.FunctorCategories 𝒯 M) where

open Setup 𝒯

open Currying 𝒯 M F

funPost : {C D E : CAT} → MAP D E → MAP (Fun C D) (Fun C E)
funPost {C} {D} g = funCurry (g ∘ funEval)

funPre : {B C D : CAT} → MAP B C → MAP (Fun C D) (Fun B D)
funPre {C = C} {D} f = funCurry 
  (funEval ∘ productMap (id (Fun C D)) f)

funPost-β : {C D E : CAT} (g : MAP D E)
  → (funUncurry (funPost {C = C} g)) =₁ (g ∘ funEval)
funPost-β {C} {D} g = funCurry-β (g ∘ funEval)

funPre-β : {B C D : CAT} (f : MAP B C)
  → (funUncurry (funPre {D = D} f)) =₁
      (funEval ∘ productMap (id (Fun C D)) f)
funPre-β {C = C} {D} f = funCurry-β 
  (funEval ∘ productMap (id (Fun C D)) f)

funPost-cong : {C D E : CAT} {g g′ : MAP D E}
  → g =₁ g′ → (funPost {C = C} g) =₁ (funPost g′)
funPost-cong {C} {D} {g = g} {g′} γ =
  funReflect (funPost g) (funPost g′)
    ((funPost-β g′) ⁻¹ ∙ ((γ ▷ funEval) ∙ funPost-β g))

funPre-cong : {B C D : CAT} {f f′ : MAP B C}
  → f =₁ f′ → (funPre {D = D} f) =₁ (funPre f′)
funPre-cong {C = C} {D} {f} {f′} φ =
  funReflect (funPre f) (funPre f′)
    ((funPre-β f′) ⁻¹ ∙
      ((funEval ◁ productMap-cong (idIso (id (Fun C D))) φ) ∙ funPre-β f))

funPost-uncurry : {X C D E : CAT} (g : MAP D E) (h : MAP X (Fun C D))
  → (funUncurry (funPost g ∘ h)) =₁ (g ∘ funUncurry h)
funPost-uncurry {C = C} g h =
  comp-assoc (productMap h (id C)) funEval g ∙
    ((funPost-β g ▷ productMap h (id C)) ∙ funUncurry-restrict (funPost g) h)
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

funPre-uncurry : {X B C D : CAT} (f : MAP B C) (h : MAP X (Fun C D))
  → (funUncurry (funPre f ∘ h)) =₁
      (funUncurry h ∘ productMap (id X) f)
funPre-uncurry {X} {B} {C} {D} f h =
  (comp-assoc (productMap (id X) f) (productMap h (id C)) funEval) ⁻¹ ∙
  ((funEval ◁ productMap-separate h f) ∙
  (comp-assoc (productMap h (id B)) (productMap (id (Fun C D)) f) funEval ∙
  ((funPre-β f ▷ productMap h (id B)) ∙ funUncurry-restrict (funPre f) h)))
```

The identity and composition laws now follow by uncurrying and lifting.
Reflection applies at every category of parameters.

```agda
funPost-id : (C D : CAT) → (funPost {C = C} (id D)) =₁ (id (Fun C D))
funPost-id C D = funReflect _ _
  ((funUncurry-id C D) ⁻¹ ∙ (comp-unitˡ funEval ∙ funPost-β (id D)))

funPre-id : (C D : CAT) → (funPre {D = D} (id C)) =₁ (id (Fun C D))
funPre-id C D = funReflect _ _
  ((funUncurry-id C D) ⁻¹ ∙
    (comp-unitʳ funEval ∙ ((funEval ◁ productMap-id (Fun C D) C) ∙ funPre-β (id C))))

funPost-comp : {A B C D : CAT} (f : MAP B C) (g : MAP C D)
  → (funPost {C = A} g ∘ funPost f) =₁ (funPost (g ∘ f))
funPost-comp {A} {B} f g = funReflect _ _
  ((funPost-β (g ∘ f)) ⁻¹ ∙
  ((comp-assoc funEval f g) ⁻¹ ∙
  ((g ◁ funPost-β f) ∙ funPost-uncurry g (funPost f))))

funPre-comp : {A B C D : CAT} (f : MAP A B) (g : MAP B C)
  → (funPre {D = D} f ∘ funPre g) =₁ (funPre (g ∘ f))
funPre-comp {C = C} {D} f g = funReflect _ _
  ((funPre-β (g ∘ f)) ⁻¹ ∙
  ((funEval ◁ (productMap-cong (comp-unitˡ (id (Fun C D))) (idIso (g ∘ f)) ∙
     productMap-comp (id (Fun C D)) (id (Fun C D)) f g)) ∙
  (comp-assoc (productMap (id (Fun C D)) f) (productMap (id (Fun C D)) g) funEval ∙
  ((funPre-β g ▷ productMap (id (Fun C D)) f) ∙ funPre-uncurry f (funPre g)))))
```

An inverse functor induces an inverse on functor categories. The inverse
comparisons use the composition and identity comparisons just proved.

```agda
funPost-isEquiv : {A C D : CAT} (f : MAP C D) → IsEquiv f
  → IsEquiv (funPost {C = A} f)
funPost-isEquiv {A} {C} {D} f e = record
  { inverse = funPost (IsEquiv.inverse e)
  ; sectionIso = (funPost-comp f (IsEquiv.inverse e)) ⁻¹ ∙
      (funPost-cong (IsEquiv.sectionIso e) ∙ (funPost-id A C) ⁻¹)
  ; retractionIso = (funPost-comp (IsEquiv.inverse e) f) ⁻¹ ∙
      (funPost-cong (IsEquiv.retractionIso e) ∙ (funPost-id A D) ⁻¹)
  }

funPre-isEquiv : {C D E : CAT} (f : MAP C D) → IsEquiv f
  → IsEquiv (funPre {D = E} f)
funPre-isEquiv {C} {D} {E} f e = record
  { inverse = funPre (IsEquiv.inverse e)
  ; sectionIso = (funPre-comp (IsEquiv.inverse e) f) ⁻¹ ∙
      (funPre-cong (IsEquiv.retractionIso e) ∙ (funPre-id D E) ⁻¹)
  ; retractionIso = (funPre-comp f (IsEquiv.inverse e)) ⁻¹ ∙
      (funPre-cong (IsEquiv.sectionIso e) ∙ (funPre-id C E) ⁻¹)
  }
```




