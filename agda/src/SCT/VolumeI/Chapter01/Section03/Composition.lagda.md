# Composition and application

Composition of mapping terms is represented by an actual functor obtained
by currying double evaluation. Application is evaluation after pairing.
Both operations accept terms with any common parameter category.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as MappingAnimae

module SCT.VolumeI.Chapter01.Section03.Composition
  {c m a : Level} (𝒯 : Theory c m a)
  (M : MappingAnimae.MappingAnimae 𝒯) where

open Setup 𝒯
open MappingAnimae.MappingAnimae M

applyTerm : {Γ C D : CAT} → MAP Γ (Map C D) → MAP Γ C → MAP Γ D
applyTerm f x = mapEval ∘ pair f x

doubleEvaluation : {C D E : CAT} → MAP ((Map D E × Map C D) × C) E
doubleEvaluation = applyTerm (pr₁ ∘ pr₁) (applyTerm (pr₂ ∘ pr₁) pr₂)

mapComp : {C D E : CAT} → MAP (Map D E × Map C D) (Map C E)
mapComp {C} {D} {E} =
  mapCurry (product-isAn (map-isAn D E) (map-isAn C D)) doubleEvaluation

mapComp-β : {C D E : CAT} → NatIso (mapUncurry (mapComp {C} {D} {E})) doubleEvaluation
mapComp-β {C} {D} {E} =
  mapCurry-β (product-isAn (map-isAn D E) (map-isAn C D)) doubleEvaluation

mapId : (C : CAT) → ObjAbs (Map C C)
mapId C = mapCurry one-isAn pr₂

mapId-β : (C : CAT) → NatIso (mapUncurry (mapId C)) pr₂
mapId-β C = mapCurry-β one-isAn pr₂

composeTerm : {Γ C D E : CAT}
  → MAP Γ (Map D E) → MAP Γ (Map C D) → MAP Γ (Map C E)
composeTerm g f = mapComp ∘ pair g f

identityTerm : {Γ : CAT} (C : CAT) → MAP Γ (Map C C)
identityTerm C = const (mapId C)

applyTerm-cong : {Γ C D : CAT} {f g : MAP Γ (Map C D)} {x y : MAP Γ C}
  → NatIso f g → NatIso x y → NatIso (applyTerm f x) (applyTerm g y)
applyTerm-cong α β = mapEval ◁ pair-cong α β

applyTerm-pre : {Γ Δ C D : CAT} (f : MAP Γ (Map C D)) (x : MAP Γ C) (σ : MAP Δ Γ)
  → NatIso (applyTerm f x ∘ σ) (applyTerm (f ∘ σ) (x ∘ σ))
applyTerm-pre f x σ = (mapEval ◁ pair-pre f x σ) ∙ comp-assoc σ (pair f x) mapEval

composeTerm-cong : {Γ C D E : CAT}
  {g g′ : MAP Γ (Map D E)} {f f′ : MAP Γ (Map C D)}
  → NatIso g g′ → NatIso f f′ → NatIso (composeTerm g f) (composeTerm g′ f′)
composeTerm-cong α β = mapComp ◁ pair-cong α β

composeTerm-pre : {Γ Δ C D E : CAT}
  (g : MAP Γ (Map D E)) (f : MAP Γ (Map C D)) (σ : MAP Δ Γ)
  → NatIso (composeTerm g f ∘ σ) (composeTerm (g ∘ σ) (f ∘ σ))
composeTerm-pre g f σ = (mapComp ◁ pair-pre g f σ) ∙ comp-assoc σ (pair g f) mapComp
```

The next comparisons spell out evaluation at a specified parameter and
argument. They use the product beta comparisons and the external associator.

```agda
productMap-pair : {Γ A B C D : CAT}
  (f : MAP A B) (g : MAP C D) (p : MAP Γ A) (q : MAP Γ C)
  → NatIso (productMap f g ∘ pair p q) (pair (f ∘ p) (g ∘ q))
productMap-pair f g p q = pair-cong
  ((f ◁ pair-β₁ p q) ∙ comp-assoc (pair p q) pr₁ f)
  ((g ◁ pair-β₂ p q) ∙ comp-assoc (pair p q) pr₂ g)
  ∙ pair-pre (f ∘ pr₁) (g ∘ pr₂) (pair p q)

mapUncurry-at : {Γ X C D : CAT}
  (f : MAP X (Map C D)) (p : MAP Γ X) (x : MAP Γ C)
  → NatIso (mapUncurry f ∘ pair p x) (applyTerm (f ∘ p) x)
mapUncurry-at {C = C} f p x =
  (mapEval ◁ (pair-cong (idIso (f ∘ p)) (comp-unitˡ x) ∙
    productMap-pair f (id C) p x)) ∙
    comp-assoc (pair p x) (productMap f (id C)) mapEval

mapUncurry-as-apply : {Γ C D : CAT} (f : MAP Γ (Map C D))
  → NatIso (mapUncurry f) (applyTerm (f ∘ pr₁) pr₂)
mapUncurry-as-apply f = mapEval ◁ pair-cong (idIso (f ∘ pr₁)) (comp-unitˡ pr₂)

apply-compose : {Γ C D E : CAT}
  (g : MAP Γ (Map D E)) (f : MAP Γ (Map C D)) (x : MAP Γ C)
  → NatIso (applyTerm (composeTerm g f) x) (applyTerm g (applyTerm f x))
apply-compose g f x =
  let point = pair (pair g f) x
      first = pair-β₁ g f ∙
        ((pr₁ ◁ pair-β₁ (pair g f) x) ∙ comp-assoc point pr₁ pr₁)
      second = pair-β₂ g f ∙
        ((pr₂ ◁ pair-β₁ (pair g f) x) ∙ comp-assoc point pr₁ pr₂)
      third = pair-β₂ (pair g f) x
      inner = applyTerm-cong second third ∙ applyTerm-pre (pr₂ ∘ pr₁) pr₂ point
      outer = applyTerm-cong first inner ∙
        applyTerm-pre (pr₁ ∘ pr₁) (applyTerm (pr₂ ∘ pr₁) pr₂) point
  in outer ∙ ((mapComp-β ▷ point) ∙ invIso (mapUncurry-at mapComp (pair g f) x))

apply-identity : {Γ C : CAT} (x : MAP Γ C)
  → NatIso (applyTerm (identityTerm C) x) x
apply-identity {Γ} {C} x = pair-β₂ (terminate Γ) x ∙
  ((mapId-β C ▷ pair (terminate Γ) x) ∙
    invIso (mapUncurry-at (mapId C) (terminate Γ) x))
```
