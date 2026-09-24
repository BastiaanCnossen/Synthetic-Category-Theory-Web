# Unitors and associators for mapping composition

Each comparison is constructed by evaluating its boundary and lifting
through the specified equivalence on isomorphism animae. The image witness
of the lift is retained. Parameters are animae precisely where that lifting
rule is used.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as MappingAnimae
import SCT.VolumeI.Chapter01.Section04.Currying as Currying
import SCT.VolumeI.Chapter01.Section04.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section03.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section03.PairingUnits as PairingUnits

module SCT.VolumeI.Chapter01.Section04.InternalCoherence
  {c m a : Level} (𝒯 : Theory c m a)
  (M : MappingAnimae.MappingAnimae 𝒯) where

open Setup 𝒯
open MappingAnimae.MappingAnimae M
open Currying 𝒯 M
open MapComposition 𝒯 M
open PairingCoherence vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-triangle₁; pair-cong-triangle₂; pair-cong-Iso₂; pair-cong-comp;
         pair-iso-extensionality)
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (pair-pre-natural; cancel-left-reflect; cancel-right)
open PairingUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (cancel-right-reflect)

mapComp-β-natural : {Γ A B C : CAT}
  {r s : MAP Γ ((Map B C × Map A B) × A)} (α : r =₁ s)
  → ((mapComp-β ▷ s) ∙ (mapUncurry mapComp ◁ α)) =₂
      ((doubleEvaluation ◁ α) ∙ (mapComp-β ▷ r))
mapComp-β-natural α = interchange-at mapComp-β α

mapId-β-natural : {Γ C : CAT} {r s : MAP Γ (One × C)} (α : r =₁ s)
  → ((mapId-β C ▷ s) ∙ (mapUncurry (mapId C) ◁ α)) =₂
      ((pr₂ ◁ α) ∙ (mapId-β C ▷ r))
mapId-β-natural {C = C} α = interchange-at (mapId-β C) α

module ParameterRetaining (P : CAT) where
  retain : {C D : CAT} → MAP (P × C) D → MAP (P × C) (P × D)
  retain f = pair pr₁ f

  retain-cong : {C D : CAT} {f g : MAP (P × C) D}
    → f =₁ g → (retain f) =₁ (retain g)
  retain-cong α = pair-cong (idIso pr₁) α

  retain-projection : {C D : CAT} (f : MAP (P × C) D)
    → (pr₁ ∘ retain f) =₁ pr₁
  retain-projection f = pair-β₁ pr₁ f

  retain-evaluation : {C D : CAT} (f : MAP (P × C) D)
    → (pr₂ ∘ retain f) =₁ f
  retain-evaluation f = pair-β₂ pr₁ f

  retain-compose : {C D E : CAT} (g : MAP (P × D) E) (f : MAP (P × C) D)
    → (retain g ∘ retain f) =₁ (retain (g ∘ retain f))
  retain-compose g f = pair-cong (retain-projection f) (idIso (g ∘ retain f)) ∙
    pair-pre pr₁ g (retain f)

  retain-id : (C : CAT) → (retain {C} pr₂) =₁ (id (P × C))
  retain-id C = pair-projections

  retain-compose-natural : {C D E : CAT}
    {g g′ : MAP (P × D) E} {f f′ : MAP (P × C) D}
    (α : g =₁ g′) (β : f =₁ f′)
    →
        (retain-compose g′ f′ ∙ (retain-cong α ⋆ retain-cong β)) =₂
        (retain-cong (α ⋆ retain-cong β) ∙ retain-compose g f)
  retain-compose-natural {g = g} {g′} {f} {f′} α β =
    let δ = retain-cong β
        changed = α ⋆ δ
        before = pair-pre pr₁ g (retain f)
        after = pair-pre pr₁ g′ (retain f′)
        normalize-before = pair-cong (retain-projection f) (idIso (g ∘ retain f))
        normalize-after = pair-cong (retain-projection f′) (idIso (g′ ∘ retain f′))
        natural = pair-pre-natural (idIso pr₁) α δ
        horizontal-unit = isoComp-unitˡ-at (pr₁ ◁ δ) ∙
          isoComp-cong (preWhisker-idIso pr₁ (retain f′)) (idIso (pr₁ ◁ δ))
        first = isoComp-unitˡ-at (retain-projection f) ∙
          (pair-cong-triangle₁ (idIso pr₁) β ∙
            isoComp-cong (idIso (retain-projection f′)) horizontal-unit)
        left-normal = isoComp-cong
          (pair-cong-Iso₂ first (isoComp-unitˡ-at changed) ∙
            (pair-cong-comp (retain-projection f′) (idIso pr₁ ⋆ δ)
              (idIso (g′ ∘ retain f′)) changed) ⁻¹) (idIso before) ∙
          ((isoComp-assoc-at normalize-after (pair-cong (idIso pr₁ ⋆ δ) changed) before) ⁻¹ ∙
          (isoComp-cong (idIso normalize-after) (natural ⁻¹) ∙
            isoComp-assoc-at normalize-after after (retain-cong α ⋆ δ)))
        right-normal = isoComp-cong
          (pair-cong-Iso₂ (isoComp-unitˡ-at (retain-projection f)) (isoComp-unitʳ-at changed) ∙
            (pair-cong-comp (idIso pr₁) (retain-projection f)
              changed (idIso (g ∘ retain f))) ⁻¹) (idIso before) ∙
          (isoComp-assoc-at (retain-cong changed) normalize-before before) ⁻¹
    in right-normal ⁻¹ ∙ left-normal

evaluate-compose : {P C D E : CAT}
  (g : MAP P (Map D E)) (f : MAP P (Map C D))
  → (mapUncurry (composeTerm g f)) =₁
      (applyTerm (g ∘ pr₁) (applyTerm (f ∘ pr₁) pr₂))
evaluate-compose g f = apply-compose (g ∘ pr₁) (f ∘ pr₁) pr₂ ∙
  (applyTerm-cong (composeTerm-pre g f pr₁) (idIso pr₂) ∙
    mapUncurry-as-apply (composeTerm g f))

uncurry-compose : {P C D E : CAT}
  (g : MAP P (Map D E)) (f : MAP P (Map C D))
  → (mapUncurry (composeTerm g f)) =₁
      (mapUncurry g ∘ ParameterRetaining.retain P (mapUncurry f))
uncurry-compose g f = (mapUncurry-at g pr₁ (mapUncurry f)) ⁻¹ ∙
  (applyTerm-cong (idIso (g ∘ pr₁)) ((mapUncurry-as-apply f) ⁻¹) ∙
    evaluate-compose g f)

uncurry-identity : (P C : CAT) → (mapUncurry (identityTerm {P} C)) =₁ pr₂
uncurry-identity P C = apply-identity pr₂ ∙
  (applyTerm-cong (const-pre (mapId C) pr₁) (idIso pr₂) ∙
    mapUncurry-as-apply (identityTerm {P} C))

module RetainedEvaluation (P : CAT) where
  open ParameterRetaining P

  retained : {C D : CAT} → MAP P (Map C D) → MAP (P × C) (P × D)
  retained f = retain (mapUncurry f)

  retained-compose : {C D E : CAT}
    (g : MAP P (Map D E)) (f : MAP P (Map C D))
    → (retained (composeTerm g f)) =₁ (retained g ∘ retained f)
  retained-compose g f = (retain-compose (mapUncurry g) (mapUncurry f)) ⁻¹ ∙
    retain-cong (uncurry-compose g f)

  retained-identity : (C : CAT)
    → (retained (identityTerm C)) =₁ (id (P × C))
  retained-identity C = retain-id C ∙ retain-cong (uncurry-identity P C)

  forget-comparison : {C D : CAT} {f g : MAP P (Map C D)}
    → (retained f) =₁ (retained g) → (mapUncurry f) =₁ (mapUncurry g)
  forget-comparison {f = f} {g} α = retain-evaluation (mapUncurry g) ∙
    ((pr₂ ◁ α) ∙ (retain-evaluation (mapUncurry f)) ⁻¹)

  retainedIso : {C D : CAT} {f g : MAP P (Map C D)}
    → f =₁ g → (retained f) =₁ (retained g)
  retainedIso α = retain-cong (mapUncurryIso α)

  forget-retainedIso : {C D : CAT} {f g : MAP P (Map C D)} (α : f =₁ g)
    → (forget-comparison (retainedIso α)) =₂ (mapUncurryIso α)
  forget-retainedIso {f = f} {g} α =
    cancel-right (retain-evaluation (mapUncurry f)) (mapUncurryIso α) ∙
      (isoComp-cong (pair-cong-triangle₂ (idIso pr₁) (mapUncurryIso α))
        (idIso ((retain-evaluation (mapUncurry f)) ⁻¹)) ∙
        (isoComp-assoc-at (retain-evaluation (mapUncurry g))
          (pr₂ ◁ retainedIso α) ((retain-evaluation (mapUncurry f)) ⁻¹)) ⁻¹)

  forget-reflect-second : {C D : CAT} {f g : MAP P (Map C D)}
    {α β : (retained f) =₁ (retained g)}
    → (forget-comparison α) =₂ (forget-comparison β)
    → (pr₂ ◁ α) =₂ (pr₂ ◁ β)
  forget-reflect-second {f = f} {g} p =
    cancel-right-reflect ((retain-evaluation (mapUncurry f)) ⁻¹)
      (cancel-left-reflect (retain-evaluation (mapUncurry g)) p)

  BaseCompatible : {C D : CAT} {f g : MAP P (Map C D)}
    → (retained f) =₁ (retained g) → Set m
  BaseCompatible {f = f} {g} α =
    (retain-projection (mapUncurry g) ∙ (pr₁ ◁ α)) =₂ (retain-projection (mapUncurry f))

  retainedIso-base : {C D : CAT} {f g : MAP P (Map C D)} (α : f =₁ g)
    → BaseCompatible (retainedIso α)
  retainedIso-base {f = f} α = isoComp-unitˡ-at (retain-projection (mapUncurry f)) ∙
    pair-cong-triangle₁ (idIso pr₁) (mapUncurryIso α)

  retained-reflect : {C D : CAT} (pAn : isAn P) {f g : MAP P (Map C D)}
    → (retained f) =₁ (retained g) → f =₁ g
  retained-reflect pAn {f} {g} α = mapReflect pAn f g (forget-comparison α)

  retained-reflect-β₂ : {C D : CAT} (pAn : isAn P) {f g : MAP P (Map C D)}
    (α : (retained f) =₁ (retained g))
    → (pr₂ ◁ retainedIso (retained-reflect pAn α)) =₂ (pr₂ ◁ α)
  retained-reflect-β₂ pAn {f} {g} α = forget-reflect-second
    (mapReflect-β pAn f g (forget-comparison α) ∙ forget-retainedIso (retained-reflect pAn α))

  retained-reflect-β : {C D : CAT} (pAn : isAn P) {f g : MAP P (Map C D)}
    (α : (retained f) =₁ (retained g))
    → BaseCompatible α → (retainedIso (retained-reflect pAn α)) =₂ α
  retained-reflect-β pAn {g = g} α compatible = pair-iso-extensionality
    (cancel-left-reflect (retain-projection (mapUncurry g))
      (compatible ⁻¹ ∙ retainedIso-base (retained-reflect pAn α)))
    (retained-reflect-β₂ pAn α)

  left-unit-route : {C D : CAT} (f : MAP P (Map C D))
    → (retained (composeTerm (identityTerm D) f)) =₁ (retained f)
  left-unit-route {D = D} f = comp-unitˡ (retained f) ∙
    ((retained-identity D ▷ retained f) ∙ retained-compose (identityTerm D) f)

  right-unit-route : {C D : CAT} (f : MAP P (Map C D))
    → (retained (composeTerm f (identityTerm C))) =₁ (retained f)
  right-unit-route {C = C} f = comp-unitʳ (retained f) ∙
    ((retained f ◁ retained-identity C) ∙ retained-compose f (identityTerm C))

  associator-route : {A B C D : CAT}
    (h : MAP P (Map C D)) (g : MAP P (Map B C)) (f : MAP P (Map A B))
    → (retained (composeTerm (composeTerm h g) f)) =₁
        (retained (composeTerm h (composeTerm g f)))
  associator-route h g f = (retained-compose h (composeTerm g f)) ⁻¹ ∙
    ((retained h ◁ retained-compose g f) ⁻¹ ∙
    (comp-assoc (retained f) (retained g) (retained h) ∙
    ((retained-compose h g ▷ retained f) ∙ retained-compose (composeTerm h g) f)))

evaluate-retained-left-unit : {P C D : CAT} (f : MAP P (Map C D))
  → (mapUncurry (composeTerm (identityTerm D) f)) =₁ (mapUncurry f)
evaluate-retained-left-unit {P} f =
  RetainedEvaluation.forget-comparison P (RetainedEvaluation.left-unit-route P f)

evaluate-retained-right-unit : {P C D : CAT} (f : MAP P (Map C D))
  → (mapUncurry (composeTerm f (identityTerm C))) =₁ (mapUncurry f)
evaluate-retained-right-unit {P} f =
  RetainedEvaluation.forget-comparison P (RetainedEvaluation.right-unit-route P f)

evaluate-left-unit : {P C D : CAT} (f : MAP P (Map C D))
  → (mapUncurry (composeTerm (identityTerm D) f)) =₁ (mapUncurry f)
evaluate-left-unit {D = D} f = (mapUncurry-as-apply f) ⁻¹ ∙
  (apply-identity (applyTerm (f ∘ pr₁) pr₂) ∙
  (applyTerm-cong (const-pre (mapId D) pr₁) (idIso (applyTerm (f ∘ pr₁) pr₂)) ∙
    evaluate-compose (identityTerm D) f))

evaluate-right-unit : {P C D : CAT} (f : MAP P (Map C D))
  → (mapUncurry (composeTerm f (identityTerm C))) =₁ (mapUncurry f)
evaluate-right-unit {C = C} f = (mapUncurry-as-apply f) ⁻¹ ∙
  (applyTerm-cong (idIso (f ∘ pr₁))
    (apply-identity pr₂ ∙ applyTerm-cong (const-pre (mapId C) pr₁) (idIso pr₂)) ∙
    evaluate-compose f (identityTerm C))

compose-unitˡ : {P C D : CAT} (pAn : isAn P) (f : MAP P (Map C D))
  → (composeTerm (identityTerm D) f) =₁ f
compose-unitˡ pAn f = mapReflect pAn _ f (evaluate-retained-left-unit f)

compose-unitʳ : {P C D : CAT} (pAn : isAn P) (f : MAP P (Map C D))
  → (composeTerm f (identityTerm C)) =₁ f
compose-unitʳ pAn f = mapReflect pAn _ f (evaluate-retained-right-unit f)

compose-unitˡ-β : {P C D : CAT} (pAn : isAn P) (f : MAP P (Map C D))
  → (mapUncurryIso (compose-unitˡ pAn f)) =₂ (evaluate-retained-left-unit f)
compose-unitˡ-β pAn f = mapReflect-β pAn _ f (evaluate-retained-left-unit f)

compose-unitʳ-β : {P C D : CAT} (pAn : isAn P) (f : MAP P (Map C D))
  → (mapUncurryIso (compose-unitʳ pAn f)) =₂ (evaluate-retained-right-unit f)
compose-unitʳ-β pAn f = mapReflect-β pAn _ f (evaluate-retained-right-unit f)
```

For three composable variables, both parenthesizations evaluate to the
same nested application expression. We retain those useful comparisons
below. The chosen associator instead uses `associator-route`, which
transports the primitive associator between parameter-retaining functors,
as in the book.

```agda
evaluate-assoc-left : {P A B C D : CAT}
  (h : MAP P (Map C D)) (g : MAP P (Map B C)) (f : MAP P (Map A B))
  → (mapUncurry (composeTerm (composeTerm h g) f)) =₁
      (applyTerm (h ∘ pr₁) (applyTerm (g ∘ pr₁) (applyTerm (f ∘ pr₁) pr₂)))
evaluate-assoc-left h g f =
  apply-compose (h ∘ pr₁) (g ∘ pr₁) (applyTerm (f ∘ pr₁) pr₂) ∙
  (applyTerm-cong (composeTerm-pre h g pr₁) (idIso (applyTerm (f ∘ pr₁) pr₂)) ∙
    evaluate-compose (composeTerm h g) f)

evaluate-assoc-right : {P A B C D : CAT}
  (h : MAP P (Map C D)) (g : MAP P (Map B C)) (f : MAP P (Map A B))
  → (mapUncurry (composeTerm h (composeTerm g f))) =₁
      (applyTerm (h ∘ pr₁) (applyTerm (g ∘ pr₁) (applyTerm (f ∘ pr₁) pr₂)))
evaluate-assoc-right h g f =
  applyTerm-cong (idIso (h ∘ pr₁))
    (apply-compose (g ∘ pr₁) (f ∘ pr₁) pr₂ ∙
      applyTerm-cong (composeTerm-pre g f pr₁) (idIso pr₂)) ∙
    evaluate-compose h (composeTerm g f)

evaluate-assoc-by-application : {P A B C D : CAT}
  (h : MAP P (Map C D)) (g : MAP P (Map B C)) (f : MAP P (Map A B))
  → (mapUncurry (composeTerm (composeTerm h g) f)) =₁
      (mapUncurry (composeTerm h (composeTerm g f)))
evaluate-assoc-by-application h g f = (evaluate-assoc-right h g f) ⁻¹ ∙ evaluate-assoc-left h g f

evaluate-assoc : {P A B C D : CAT}
  (h : MAP P (Map C D)) (g : MAP P (Map B C)) (f : MAP P (Map A B))
  → (mapUncurry (composeTerm (composeTerm h g) f)) =₁
      (mapUncurry (composeTerm h (composeTerm g f)))
evaluate-assoc {P} h g f =
  RetainedEvaluation.forget-comparison P (RetainedEvaluation.associator-route P h g f)

compose-assoc : {P A B C D : CAT} (pAn : isAn P)
  (h : MAP P (Map C D)) (g : MAP P (Map B C)) (f : MAP P (Map A B))
  → (composeTerm (composeTerm h g) f) =₁ (composeTerm h (composeTerm g f))
compose-assoc pAn h g f = mapReflect pAn _ _ (evaluate-assoc h g f)

compose-assoc-β : {P A B C D : CAT} (pAn : isAn P)
  (h : MAP P (Map C D)) (g : MAP P (Map B C)) (f : MAP P (Map A B))
  → (mapUncurryIso (compose-assoc pAn h g f)) =₂ (evaluate-assoc h g f)
compose-assoc-β pAn h g f = mapReflect-β pAn _ _ (evaluate-assoc h g f)

mapComp-unitˡ : (C D : CAT)
  → (composeTerm (identityTerm D) (id (Map C D))) =₁ (id (Map C D))
mapComp-unitˡ C D = compose-unitˡ (map-isAn C D) (id (Map C D))

mapComp-unitʳ : (C D : CAT)
  → (composeTerm (id (Map C D)) (identityTerm C)) =₁ (id (Map C D))
mapComp-unitʳ C D = compose-unitʳ (map-isAn C D) (id (Map C D))

mapComp-assoc : (A B C D : CAT)
  → let P = (Map C D × Map B C) × Map A B
        h : MAP P (Map C D)
        h = pr₁ ∘ pr₁
        g : MAP P (Map B C)
        g = pr₂ ∘ pr₁
        f : MAP P (Map A B)
        f = pr₂
    in (composeTerm (composeTerm h g) f) =₁ (composeTerm h (composeTerm g f))
mapComp-assoc A B C D =
  compose-assoc (product-isAn (product-isAn (map-isAn C D) (map-isAn B C)) (map-isAn A B))
    (pr₁ ∘ pr₁) (pr₂ ∘ pr₁) pr₂
```

The displayed universal comparisons also act on terms with arbitrary
common parameter. This uses substitution into those comparisons, rather
than applying the currying rule with a non-anima parameter.

```agda
composeTerm-evaluate : {Γ Δ A B C : CAT}
  (g : MAP Γ (Map B C)) (f : MAP Γ (Map A B)) (σ : MAP Δ Γ)
  {g′ : MAP Δ (Map B C)} {f′ : MAP Δ (Map A B)}
  → (g ∘ σ) =₁ g′ → (f ∘ σ) =₁ f′
  → (composeTerm g f ∘ σ) =₁ (composeTerm g′ f′)
composeTerm-evaluate g f σ α β = composeTerm-cong α β ∙ composeTerm-pre g f σ

internalUnitˡ : {Γ C D : CAT} (f : MAP Γ (Map C D))
  → (composeTerm (identityTerm D) f) =₁ f
internalUnitˡ {C = C} {D} f = specialize (mapComp-unitˡ C D) f
  (composeTerm-evaluate (identityTerm D) (id (Map C D)) f
    (const-pre (mapId D) f) (comp-unitˡ f))
  (comp-unitˡ f)

internalUnitʳ : {Γ C D : CAT} (f : MAP Γ (Map C D))
  → (composeTerm f (identityTerm C)) =₁ f
internalUnitʳ {C = C} {D} f = specialize (mapComp-unitʳ C D) f
  (composeTerm-evaluate (id (Map C D)) (identityTerm C) f
    (comp-unitˡ f) (const-pre (mapId C) f))
  (comp-unitˡ f)

internalAssoc : {Γ A B C D : CAT}
  (h : MAP Γ (Map C D)) (g : MAP Γ (Map B C)) (f : MAP Γ (Map A B))
  → (composeTerm (composeTerm h g) f) =₁ (composeTerm h (composeTerm g f))
internalAssoc {A = A} {B} {C} {D} h g f =
  let point = pair (pair h g) f
      first = pair-β₁ h g ∙
        ((pr₁ ◁ pair-β₁ (pair h g) f) ∙ comp-assoc point pr₁ pr₁)
      second = pair-β₂ h g ∙
        ((pr₂ ◁ pair-β₁ (pair h g) f) ∙ comp-assoc point pr₁ pr₂)
      third = pair-β₂ (pair h g) f
  in specialize (mapComp-assoc A B C D) point
    (composeTerm-evaluate (composeTerm (pr₁ ∘ pr₁) (pr₂ ∘ pr₁)) pr₂ point
      (composeTerm-evaluate (pr₁ ∘ pr₁) (pr₂ ∘ pr₁) point first second) third)
    (composeTerm-evaluate (pr₁ ∘ pr₁) (composeTerm (pr₂ ∘ pr₁) pr₂) point first
      (composeTerm-evaluate (pr₂ ∘ pr₁) pr₂ point second third))
```

The following are the precise pentagon and triangle boundaries for these
chosen comparisons. They do not assume the identities. In particular,
constructing and lifting the individual associators above does not yet
prove that their five occurrences form a commuting pentagon.

```agda
module Pentagon {Γ A B C D E : CAT}
  (k : MAP Γ (Map D E)) (h : MAP Γ (Map C D))
  (g : MAP Γ (Map B C)) (f : MAP Γ (Map A B)) where

  source = composeTerm (composeTerm (composeTerm k h) g) f
  target = composeTerm k (composeTerm h (composeTerm g f))

  short : source =₁ target
  short = internalAssoc k h (composeTerm g f) ∙ internalAssoc (composeTerm k h) g f

  long : source =₁ target
  long = (composeTerm-cong (idIso k) (internalAssoc h g f) ∙
    internalAssoc k (composeTerm h g) f) ∙
    composeTerm-cong (internalAssoc k h g) (idIso f)

  Statement : Set m
  Statement = short =₂ long

  by-evaluation : (γAn : isAn Γ)
    → (mapUncurryIso short) =₂ (mapUncurryIso long) → Statement
  by-evaluation γAn = mapReflect-Iso₂ γAn short long

module Triangle {Γ A B C : CAT}
  (g : MAP Γ (Map B C)) (f : MAP Γ (Map A B)) where

  source = composeTerm (composeTerm g (identityTerm B)) f
  target = composeTerm g f

  short : source =₁ target
  short = composeTerm-cong (internalUnitʳ g) (idIso f)

  long : source =₁ target
  long = composeTerm-cong (idIso g) (internalUnitˡ f) ∙ internalAssoc g (identityTerm B) f

  Statement : Set m
  Statement = short =₂ long

  by-evaluation : (γAn : isAn Γ)
    → (mapUncurryIso short) =₂ (mapUncurryIso long) → Statement
  by-evaluation γAn = mapReflect-Iso₂ γAn short long
```
