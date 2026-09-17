# Functoriality of functor categories

Postcomposition and precomposition are obtained by currying evaluation.
Their formulas on an arbitrary category of parameters are proved before the
composition laws. In this way the composition laws compare actual functors
between functor categories, rather than just their absolute points.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.Currying as Currying

import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section06.Functoriality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) (F : Categories.FunctorCategories 𝒯 M) where

open Setup 𝒯

open Currying 𝒯 M F

funPost : {C D E : CAT} → MAP D E → MAP (Fun C D) (Fun C E)
funPost {C} {D} g = funCurry (g ∘ funEval)

funPre : {B C D : CAT} → MAP B C → MAP (Fun C D) (Fun B D)
funPre {C = C} {D} f = funCurry 
  (funEval ∘ productMap (id (Fun C D)) f)

funPost-β : {C D E : CAT} (g : MAP D E)
  → NatIso (funUncurry (funPost {C = C} g)) (g ∘ funEval)
funPost-β {C} {D} g = funCurry-β (g ∘ funEval)

funPre-β : {B C D : CAT} (f : MAP B C)
  → NatIso (funUncurry (funPre {D = D} f))
      (funEval ∘ productMap (id (Fun C D)) f)
funPre-β {C = C} {D} f = funCurry-β 
  (funEval ∘ productMap (id (Fun C D)) f)

funPost-cong : {C D E : CAT} {g g′ : MAP D E}
  → NatIso g g′ → NatIso (funPost {C = C} g) (funPost g′)
funPost-cong {C} {D} {g = g} {g′} γ =
  funReflect (funPost g) (funPost g′)
    (invIso (funPost-β g′) ∙ ((γ ▷ funEval) ∙ funPost-β g))

funPre-cong : {B C D : CAT} {f f′ : MAP B C}
  → NatIso f f′ → NatIso (funPre {D = D} f) (funPre f′)
funPre-cong {C = C} {D} {f} {f′} φ =
  funReflect (funPre f) (funPre f′)
    (invIso (funPre-β f′) ∙
      ((funEval ◁ productMap-cong (idIso (id (Fun C D))) φ) ∙ funPre-β f))

funPost-uncurry : {X C D E : CAT} (g : MAP D E) (h : MAP X (Fun C D))
  → NatIso (funUncurry (funPost g ∘ h)) (g ∘ funUncurry h)
funPost-uncurry {C = C} g h =
  comp-assoc (productMap h (id C)) funEval g ∙
    ((funPost-β g ▷ productMap h (id C)) ∙ funUncurry-pre (funPost g) h)
```

For precomposition the two product maps act in different coordinates.
The following comparison retains both product composition comparisons and
the four unitors used to put them in the same form.

```agda
productMap-separate : {A B C D : CAT} (f : MAP A C) (g : MAP B D)
  → NatIso (productMap (id C) g ∘ productMap f (id B))
      (productMap f (id D) ∘ productMap (id A) g)
productMap-separate {A} {B} {C} {D} f g =
  invIso (productMap-comp (id A) f g (id D)) ∙
  (invIso (productMap-cong (comp-unitʳ f) (comp-unitˡ g)) ∙
  (productMap-cong (comp-unitˡ f) (comp-unitʳ g) ∙
   productMap-comp f (id C) (id B) g))

funPre-uncurry : {X B C D : CAT} (f : MAP B C) (h : MAP X (Fun C D))
  → NatIso (funUncurry (funPre f ∘ h))
      (funUncurry h ∘ productMap (id X) f)
funPre-uncurry {X} {B} {C} {D} f h =
  invIso (comp-assoc (productMap (id X) f) (productMap h (id C)) funEval) ∙
  ((funEval ◁ productMap-separate h f) ∙
  (comp-assoc (productMap h (id B)) (productMap (id (Fun C D)) f) funEval ∙
  ((funPre-β f ▷ productMap h (id B)) ∙ funUncurry-pre (funPre f) h)))
```

The identity and composition laws now follow by uncurrying and lifting.
Reflection applies at every category of parameters.

```agda
funPost-id : (C D : CAT) → NatIso (funPost {C = C} (id D)) (id (Fun C D))
funPost-id C D = funReflect _ _
  (invIso (funUncurry-id C D) ∙ (comp-unitˡ funEval ∙ funPost-β (id D)))

funPre-id : (C D : CAT) → NatIso (funPre {D = D} (id C)) (id (Fun C D))
funPre-id C D = funReflect _ _
  (invIso (funUncurry-id C D) ∙
    (comp-unitʳ funEval ∙ ((funEval ◁ productMap-id (Fun C D) C) ∙ funPre-β (id C))))

funPost-comp : {A B C D : CAT} (f : MAP B C) (g : MAP C D)
  → NatIso (funPost {C = A} g ∘ funPost f) (funPost (g ∘ f))
funPost-comp {A} {B} f g = funReflect _ _
  (invIso (funPost-β (g ∘ f)) ∙
  (invIso (comp-assoc funEval f g) ∙
  ((g ◁ funPost-β f) ∙ funPost-uncurry g (funPost f))))

funPre-comp : {A B C D : CAT} (f : MAP A B) (g : MAP B C)
  → NatIso (funPre {D = D} f ∘ funPre g) (funPre (g ∘ f))
funPre-comp {C = C} {D} f g = funReflect _ _
  (invIso (funPre-β (g ∘ f)) ∙
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
  ; sectionIso = invIso (funPost-comp f (IsEquiv.inverse e)) ∙
      (funPost-cong (IsEquiv.sectionIso e) ∙ invIso (funPost-id A C))
  ; retractionIso = invIso (funPost-comp (IsEquiv.inverse e) f) ∙
      (funPost-cong (IsEquiv.retractionIso e) ∙ invIso (funPost-id A D))
  }

funPre-isEquiv : {C D E : CAT} (f : MAP C D) → IsEquiv f
  → IsEquiv (funPre {D = E} f)
funPre-isEquiv {C} {D} {E} f e = record
  { inverse = funPre (IsEquiv.inverse e)
  ; sectionIso = invIso (funPre-comp (IsEquiv.inverse e) f) ∙
      (funPre-cong (IsEquiv.retractionIso e) ∙ invIso (funPre-id D E))
  ; retractionIso = invIso (funPre-comp f (IsEquiv.inverse e)) ∙
      (funPre-cong (IsEquiv.sectionIso e) ∙ invIso (funPre-id C E))
  }
```




