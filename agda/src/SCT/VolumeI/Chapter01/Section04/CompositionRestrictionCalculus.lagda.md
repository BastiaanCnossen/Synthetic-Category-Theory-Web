# Composition and change of parameter

The comparison for applying a mapping term commutes with iterated
substitution. We retain the chosen pairing comparisons and the external
associator in this calculation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section04.ProductAssociativity as ProductAssociativity
import SCT.VolumeI.Chapter01.Section04.CompositionNaturality as CompositionNaturality
import SCT.VolumeI.Chapter01.Section04.EvaluationParameterChange as EvaluationParameterChange
import SCT.VolumeI.Chapter01.Section04.Currying as Currying
import SCT.VolumeI.Chapter01.Section04.InternalCoherence as InternalCoherence
import SCT.VolumeI.Chapter01.Section04.ParameterChange as ParameterChange
import SCT.VolumeI.Chapter01.Section04.ProductSubstitution as ProductSubstitution
import SCT.VolumeI.Chapter01.Section03.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section03.ProductFunctorUnits as ProductFunctorUnits
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section03.IteratedPairing as IteratedPairing

module SCT.VolumeI.Chapter01.Section04.CompositionRestrictionCalculus
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open MapComposition 𝒯 M
open CompositionNaturality 𝒯 M
  using (coordinate-at)

open Currying 𝒯 M hiding (mapUncurry-actions-agree)
open InternalCoherence 𝒯 M using (uncurry-compose; evaluate-compose; module RetainedEvaluation)
open ParameterChange 𝒯 M using (retained-parameter-change)
open ProductSubstitution 𝒯 M using (module Coordinates)
open Structural vocabulary terminal products productLaws composition whiskering
  using (preWhisker-comp-at)
open PairingCoherence vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-id; pair-cong-comp; pair-cong-Iso₂; pair-pre-triangle₁; pair-pre-triangle₂)
open ProductFunctorUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pair-pre-cong-triangle₁; pair-pre-cong-triangle₂)
open ProductAssociativity 𝒯 M using (post-pasting; cancel-forward)
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-right; move-square; cancel-left-reflect; cancel-left)
open IteratedPairing vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pair-pre-iterated; pre-inverse-at)

open import SCT.VolumeI.Chapter01.Section04.ApplicationRestriction 𝒯 M public
  hiding (combine-apply; post-iterated-comparison)
open import SCT.VolumeI.Chapter01.Section04.MappingProofCalculus 𝒯 M public

abstract
  binary-pre-substitution : {X Y A B C : CAT} (F : MAP (A × B) C)
    (f : MAP X A) (g : MAP X B) {r s : MAP Y X} (γ : r =₁ s)
    → let before = (F ◁ pair-pre f g r) ∙ comp-assoc r (pair f g) F
          after = (F ◁ pair-pre f g s) ∙ comp-assoc s (pair f g) F
      in (after ∙ ((F ∘ pair f g) ◁ γ)) =₂
          ((F ◁ pair-cong (f ◁ γ) (g ◁ γ)) ∙ before)
  binary-pre-substitution = CompositionNaturality.binary-pre-substitution 𝒯 M

abstract
  apply-compose-natural : {Γ C D E : CAT}
    {g g′ : MAP Γ (Map D E)} {f f′ : MAP Γ (Map C D)} {x x′ : MAP Γ C}
    (α : g =₁ g′) (β : f =₁ f′) (τ : x =₁ x′)
    → (apply-compose g′ f′ x′ ∙ applyTerm-cong (composeTerm-cong α β) τ) =₂
        (applyTerm-cong α (applyTerm-cong β τ) ∙ apply-compose g f x)
  apply-compose-natural = CompositionNaturality.apply-compose-natural 𝒯 M

```
```agda
module BinaryOperation {A B Z : CAT} (F : MAP (A × B) Z) where
  term : {X : CAT} → MAP X A → MAP X B → MAP X Z
  term f x = F ∘ pair f x

  act : {X : CAT} {f g : MAP X A} {x y : MAP X B}
    → f =₁ g → x =₁ y → (term f x) =₁ (term g y)
  act α β = F ◁ pair-cong α β

  pre : {X Y : CAT} (f : MAP X A) (x : MAP X B) (r : MAP Y X)
    → (term f x ∘ r) =₁ (term (f ∘ r) (x ∘ r))
  pre f x r = (F ◁ pair-pre f x r) ∙ comp-assoc r (pair f x) F

  abstract
    act-comp : {X : CAT} {f₀ f₁ f₂ : MAP X A} {x₀ x₁ x₂ : MAP X B}
      (α₂ : f₁ =₁ f₂) (α₁ : f₀ =₁ f₁)
      (β₂ : x₁ =₁ x₂) (β₁ : x₀ =₁ x₁)
      → (act (α₂ ∙ α₁) (β₂ ∙ β₁)) =₂ (act α₂ β₂ ∙ act α₁ β₁)
    act-comp α₂ α₁ β₂ β₁ = postWhisker-isoComp-at F (pair-cong α₂ β₂) (pair-cong α₁ β₁) ∙
      (postWhisker F ◁ pair-cong-comp α₂ α₁ β₂ β₁)

  abstract
    act-Iso₂ : {X : CAT} {f g : MAP X A} {x y : MAP X B}
      {α α′ : f =₁ g} {β β′ : x =₁ y}
      → α =₂ α′ → β =₂ β′ → (act α β) =₂ (act α′ β′)
    act-Iso₂ p q = postWhisker F ◁ pair-cong-Iso₂ p q

  abstract
    act-id : {X : CAT} (f : MAP X A) (x : MAP X B)
      → (act (idIso f) (idIso x)) =₂ (idIso (term f x))
    act-id f x = postWhisker-idIso F (pair f x) ∙ (postWhisker F ◁ pair-cong-id f x)

  abstract
    combine : {X : CAT} {f₀ f₁ f₂ : MAP X A} {x₀ x₁ x₂ : MAP X B} {source : MAP X Z}
      (α : f₁ =₁ f₂) (β : x₁ =₁ x₂) (γ : f₀ =₁ f₁) (δ : x₀ =₁ x₁)
      (base : source =₁ (term f₀ x₀))
      → (act α β ∙ (act γ δ ∙ base)) =₂ (act (α ∙ γ) (β ∙ δ) ∙ base)
    combine α β γ δ base = isoComp-cong ((act-comp α γ β δ) ⁻¹) (idIso base) ∙
      (isoComp-assoc-at (act α β) (act γ δ) base) ⁻¹

  module Assembly {R Γ X : CAT}
    (H : MAP X A) (K : MAP X B)
    (q : MAP Γ X) (r : MAP R Γ) (q′ : MAP R X) (δ : (q ∘ r) =₁ q′)
    {f : MAP Γ A} {x : MAP Γ B}
    {f′ : MAP R A} {x′ : MAP R B}
    (a : (H ∘ q) =₁ f) (b : (K ∘ q) =₁ x)
    (a′ : (H ∘ q′) =₁ f′) (b′ : (K ∘ q′) =₁ x′)
    (c : (f ∘ r) =₁ f′) (d : (x ∘ r) =₁ x′) where
  
    normalization = act a b ∙ pre H K q
    normalization′ = act a′ b′ ∙ pre H K q′
  
    short = normalization′ ∙ ((term H K ◁ δ) ∙ comp-assoc r q (term H K))
    long = act c d ∙ (pre f x r ∙ (normalization ▷ r))
  
    base = pre (H ∘ q) (K ∘ q) r ∙ (pre H K q ▷ r)
  
    abstract
      short-normalization : short =₂
        (act (a′ ∙ ((H ◁ δ) ∙ comp-assoc r q H))
          (b′ ∙ ((K ◁ δ) ∙ comp-assoc r q K)) ∙ base)
      short-normalization =
        let paired = act a′ b′
            changed = act (H ◁ δ) (K ◁ δ)
            A = comp-assoc r q (term H K)
            substitute = isoComp-assoc-at changed (pre H K (q ∘ r)) A ∙
              (isoComp-cong (binary-pre-substitution F H K δ) (idIso A) ∙
                (isoComp-assoc-at (pre H K q′) (term H K ◁ δ) A) ⁻¹)
            iterate = isoComp-cong (idIso changed) (binary-pre-iterated F H K q r)
            combineInner = combine (H ◁ δ) (K ◁ δ)
              (comp-assoc r q H) (comp-assoc r q K) base
        in combine a′ b′ ((H ◁ δ) ∙ comp-assoc r q H) ((K ◁ δ) ∙ comp-assoc r q K) base ∙
          (isoComp-cong (idIso paired) (combineInner ∙ (iterate ∙ substitute)) ∙
            isoComp-assoc-at paired (pre H K q′) ((term H K ◁ δ) ∙ A))
  
    abstract
      long-normalization : long =₂
        (act (c ∙ (a ▷ r)) (d ∙ (b ▷ r)) ∙ base)
      long-normalization =
        let outer = act c d
            before = pre H K q ▷ r
            middle = pre f x r
            input = act a b ▷ r
            output = act (a ▷ r) (b ▷ r)
            exchange = isoComp-assoc-at output (pre (H ∘ q) (K ∘ q) r) before ∙
              (isoComp-cong (binary-pre-inputs F a b r) (idIso before) ∙
                (isoComp-assoc-at middle input before) ⁻¹)
        in combine c d (a ▷ r) (b ▷ r) base ∙
          (isoComp-cong (idIso outer) exchange ∙
            isoComp-cong (idIso outer) (isoComp-cong (idIso middle)
              (preWhisker-isoComp-at (act a b) (pre H K q) r)))
  
    abstract
      assemble :
        (a′ ∙ ((H ◁ δ) ∙ comp-assoc r q H)) =₂ (c ∙ (a ▷ r))
        → (b′ ∙ ((K ◁ δ) ∙ comp-assoc r q K)) =₂ (d ∙ (b ▷ r))
        → short =₂ long
      assemble first second = long-normalization ⁻¹ ∙
        (isoComp-cong (act-Iso₂ first second) (idIso base) ∙ short-normalization)
```


```agda
module BinaryFirstCoordinate {P Q A B Z : CAT} (C : CAT)
  (F : MAP (A × B) Z) (g : MAP P A) (f : MAP P B) (σ : MAP Q P) where
  open BinaryOperation F

  s = productMap σ (id C)
  δ = pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂)
  Ag = comp-assoc (pr₁ {Q} {C}) σ g
  Af = comp-assoc (pr₁ {Q} {C}) σ f
  AB = comp-assoc (pr₁ {Q} {C}) σ (term g f)
  cg = Coordinates.first C g σ
  cf = Coordinates.first C f σ
  cB = Coordinates.first C (term g f) σ
  N = act (idIso (g ∘ pr₁ {P} {C})) (idIso (f ∘ pr₁ {P} {C})) ∙ pre g f (pr₁ {P} {C})
  N′ = act (Ag ⁻¹) (Af ⁻¹) ∙ pre g f (σ ∘ pr₁ {Q} {C})
  tail = (term g f ◁ δ) ∙ comp-assoc s pr₁ (term g f)
  T = pre (g ∘ σ) (f ∘ σ) (pr₁ {Q} {C}) ∙ (pre g f σ ▷ pr₁ {Q} {C})

  abstract
    old-normalization : N =₂ (pre g f pr₁)
    old-normalization = isoComp-unitˡ-at (pre g f pr₁) ∙
      isoComp-cong (act-id (g ∘ pr₁) (f ∘ pr₁)) (idIso (pre g f pr₁))

  abstract
    new-normalization : N′ =₂ (T ∙ AB ⁻¹)
    new-normalization =
      let inverseAction = act (Ag ⁻¹) (Af ⁻¹)
          forwardAction = act Ag Af
          cancelAction = act-id ((g ∘ σ) ∘ pr₁) ((f ∘ σ) ∘ pr₁) ∙
            (act-Iso₂ (isoComp-inverseˡ-at Ag) (isoComp-inverseˡ-at Af) ∙
              (act-comp (Ag ⁻¹) Ag (Af ⁻¹) Af) ⁻¹)
          square = isoComp-unitˡ-at T ∙
            (isoComp-cong cancelAction (idIso T) ∙
              ((isoComp-assoc-at inverseAction forwardAction T) ⁻¹ ∙
                (isoComp-cong (idIso inverseAction) (binary-pre-iterated F g f σ pr₁) ∙
                  isoComp-assoc-at inverseAction (pre g f (σ ∘ pr₁)) AB)))
      in isoComp-cong square (idIso (AB ⁻¹)) ∙ (cancel-right AB N′) ⁻¹

  abstract
    compatibility :
      (pre (g ∘ σ) (f ∘ σ) pr₁ ∙ ((pre g f σ ▷ pr₁) ∙ cB)) =₂
      (act cg cf ∙ (pre (g ∘ pr₁) (f ∘ pr₁) s ∙ (pre g f pr₁ ▷ s)))
    compatibility =
      let first = (isoComp-unitʳ-at cg ∙
            isoComp-cong (idIso cg) (preWhisker-idIso (g ∘ pr₁) s)) ⁻¹
          second = (isoComp-unitʳ-at cf ∙
            isoComp-cong (idIso cf) (preWhisker-idIso (f ∘ pr₁) s)) ⁻¹
          assembled = Assembly.assemble g f pr₁ s (σ ∘ pr₁) δ
            (idIso (g ∘ pr₁)) (idIso (f ∘ pr₁)) (Ag ⁻¹) (Af ⁻¹) cg cf first second
          left = isoComp-cong (new-normalization ⁻¹) (idIso tail) ∙
            ((isoComp-assoc-at T (AB ⁻¹) tail) ⁻¹ ∙
              (isoComp-assoc-at (pre (g ∘ σ) (f ∘ σ) pr₁) (pre g f σ ▷ pr₁) cB) ⁻¹)
          right = isoComp-cong (idIso (act cg cf))
            (isoComp-cong (idIso (pre (g ∘ pr₁) (f ∘ pr₁) s)) (preWhisker s ◁ old-normalization))
      in right ∙ (assembled ∙ left)
```

The point used to evaluate the composition beta comparison is the pair
of the two mapping terms, paired with the argument. Its three projection
witnesses are compatible with restriction.

```agda
abstract
  apply-identity-action : {Γ C D : CAT} (f : MAP Γ (Map C D)) (x : MAP Γ C)
    → (applyTerm-cong (idIso f) (idIso x)) =₂ (idIso (applyTerm f x))
  apply-identity-action f x = postWhisker-idIso mapEval (pair f x) ∙
    (postWhisker mapEval ◁ pair-cong-id f x)

module CompositionPoint {R Γ C D E : CAT}
  (g : MAP Γ (Map D E)) (f : MAP Γ (Map C D)) (x : MAP Γ C) (r : MAP R Γ) where

  point = pair (pair g f) x
  point′ = pair (pair (g ∘ r) (f ∘ r)) (x ∘ r)
  pairChange = pair-pre g f r
  pointChange = pair-cong pairChange (idIso (x ∘ r)) ∙ pair-pre (pair g f) x r

  first = pair-β₁ g f ∙ coordinate-at pr₁ pr₁ point (pair-β₁ (pair g f) x)
  first′ = pair-β₁ (g ∘ r) (f ∘ r) ∙
    coordinate-at pr₁ pr₁ point′ (pair-β₁ (pair (g ∘ r) (f ∘ r)) (x ∘ r))
  second = pair-β₂ g f ∙ coordinate-at pr₂ pr₁ point (pair-β₁ (pair g f) x)
  second′ = pair-β₂ (g ∘ r) (f ∘ r) ∙
    coordinate-at pr₂ pr₁ point′ (pair-β₁ (pair (g ∘ r) (f ∘ r)) (x ∘ r))
  third = pair-β₂ (pair g f) x
  third′ = pair-β₂ (pair (g ∘ r) (f ∘ r)) (x ∘ r)

  abstract
    firstProjection :
      (pair-β₁ (pair (g ∘ r) (f ∘ r)) (x ∘ r) ∙ (pr₁ ◁ pointChange)) =₂
      (pairChange ∙ ((pair-β₁ (pair g f) x ▷ r) ∙ (comp-assoc r point pr₁) ⁻¹))
    firstProjection = pair-pre-cong-triangle₁ (pair g f) x r pairChange (idIso (x ∘ r))

    secondProjection :
      (third′ ∙ (pr₂ ◁ pointChange)) =₂
      (idIso (x ∘ r) ∙ ((third ▷ r) ∙ (comp-assoc r point pr₂) ⁻¹))
    secondProjection = pair-pre-cong-triangle₂ (pair g f) x r pairChange (idIso (x ∘ r))

  abstract
    third-restriction :
      (third′ ∙ ((pr₂ ◁ pointChange) ∙ comp-assoc r point pr₂)) =₂ (third ▷ r)
    third-restriction = isoComp-unitˡ-at (third ▷ r) ∙
      projection-square-forward pr₂ point r point′ pointChange third third′ (idIso (x ∘ r))
        secondProjection

  abstract
    nested-projection : {A : CAT} (π : MAP (Map D E × Map C D) A)
      {v : MAP Γ A} (b : (π ∘ pair g f) =₁ v)
      (b′ : (π ∘ pair (g ∘ r) (f ∘ r)) =₁ (v ∘ r))
      → (b′ ∙ (π ◁ pairChange)) =₂
          ((b ▷ r) ∙ (comp-assoc r (pair g f) π) ⁻¹)
      →
        ((b′ ∙ coordinate-at π pr₁ point′ (pair-β₁ (pair (g ∘ r) (f ∘ r)) (x ∘ r))) ∙
          (((π ∘ pr₁) ◁ pointChange) ∙ comp-assoc r point (π ∘ pr₁))) =₂
        ((b ∙ coordinate-at π pr₁ point (pair-β₁ (pair g f) x)) ▷ r)
    nested-projection π {v} b b′ triangle =
      let old = coordinate-at π pr₁ point (pair-β₁ (pair g f) x)
          new = coordinate-at π pr₁ point′ (pair-β₁ (pair (g ∘ r) (f ∘ r)) (x ∘ r))
          tail = ((π ∘ pr₁) ◁ pointChange) ∙ comp-assoc r point (π ∘ pr₁)
          A = comp-assoc r (pair g f) π
          coordinate = coordinate-restriction π pr₁ point r point′ pointChange
            (pair-β₁ (pair g f) x) (pair-β₁ (pair (g ∘ r) (f ∘ r)) (x ∘ r))
            pairChange firstProjection
          projection = isoComp-unitˡ-at (b ▷ r) ∙
            projection-square-forward π (pair g f) r (pair (g ∘ r) (f ∘ r)) pairChange b b′
              (idIso (v ∘ r)) ((isoComp-unitˡ-at _) ⁻¹ ∙ triangle)
          rearrange = (isoComp-assoc-at b′ ((π ◁ pairChange) ∙ A) (old ▷ r)) ⁻¹ ∙
            isoComp-cong (idIso b′) ((isoComp-assoc-at (π ◁ pairChange) A (old ▷ r)) ⁻¹)
      in (preWhisker-isoComp-at b old r) ⁻¹ ∙
        (isoComp-cong projection (idIso (old ▷ r)) ∙
          (rearrange ∙ (isoComp-cong (idIso b′) coordinate ∙ isoComp-assoc-at b′ new tail)))

  abstract
    first-restriction :
      (first′ ∙ (((pr₁ ∘ pr₁) ◁ pointChange) ∙ comp-assoc r point (pr₁ ∘ pr₁))) =₂
      (first ▷ r)
    first-restriction = nested-projection pr₁ (pair-β₁ g f) (pair-β₁ (g ∘ r) (f ∘ r))
      (pair-pre-triangle₁ g f r)

    second-restriction :
      (second′ ∙ (((pr₂ ∘ pr₁) ◁ pointChange) ∙ comp-assoc r point (pr₂ ∘ pr₁))) =₂
      (second ▷ r)
    second-restriction = nested-projection pr₂ (pair-β₂ g f) (pair-β₂ (g ∘ r) (f ∘ r))
      (pair-pre-triangle₂ g f r)

  inner = applyTerm-cong second third ∙ applyTerm-pre (pr₂ ∘ pr₁) pr₂ point
  inner′ = applyTerm-cong second′ third′ ∙ applyTerm-pre (pr₂ ∘ pr₁) pr₂ point′
  outer = applyTerm-cong first inner ∙
    applyTerm-pre (pr₁ ∘ pr₁) (applyTerm (pr₂ ∘ pr₁) pr₂) point
  outer′ = applyTerm-cong first′ inner′ ∙
    applyTerm-pre (pr₁ ∘ pr₁) (applyTerm (pr₂ ∘ pr₁) pr₂) point′

  abstract
    inner-restriction :
      (inner′ ∙ ((applyTerm (pr₂ ∘ pr₁) pr₂ ◁ pointChange) ∙
        comp-assoc r point (applyTerm (pr₂ ∘ pr₁) pr₂))) =₂
      (applyTerm-pre f x r ∙ (inner ▷ r))
    inner-restriction = isoComp-unitˡ-at (applyTerm-pre f x r ∙ (inner ▷ r)) ∙
      (isoComp-cong (apply-identity-action (f ∘ r) (x ∘ r)) (idIso _) ∙
        ApplicationAssembly.assemble (pr₂ ∘ pr₁) pr₂ point r point′ pointChange
          second third second′ third′ (idIso (f ∘ r)) (idIso (x ∘ r))
          ((isoComp-unitˡ-at (second ▷ r)) ⁻¹ ∙ second-restriction)
          ((isoComp-unitˡ-at (third ▷ r)) ⁻¹ ∙ third-restriction))

  abstract
    outer-restriction :
      (outer′ ∙ ((doubleEvaluation ◁ pointChange) ∙ comp-assoc r point doubleEvaluation)) =₂
      (applyTerm-cong (idIso (g ∘ r)) (applyTerm-pre f x r) ∙
        (applyTerm-pre g (applyTerm f x) r ∙ (outer ▷ r)))
    outer-restriction = ApplicationAssembly.assemble
      (pr₁ ∘ pr₁) (applyTerm (pr₂ ∘ pr₁) pr₂) point r point′ pointChange
      first inner first′ inner′ (idIso (g ∘ r)) (applyTerm-pre f x r)
      ((isoComp-unitˡ-at (first ▷ r)) ⁻¹ ∙ first-restriction) inner-restriction
```

```agda
abstract
  comparison-restriction : {R Γ X Y : CAT} {F G : MAP X Y}
    (α : F =₁ G) (q : MAP Γ X) (r : MAP R Γ) (q′ : MAP R X)
    (δ : (q ∘ r) =₁ q′)
    → ((α ▷ q′) ∙ ((F ◁ δ) ∙ comp-assoc r q F)) =₂
        (((G ◁ δ) ∙ comp-assoc r q G) ∙ ((α ▷ q) ▷ r))
  comparison-restriction {F = F} {G} α q r q′ δ =
    (isoComp-assoc-at (G ◁ δ) (comp-assoc r q G) ((α ▷ q) ▷ r)) ⁻¹ ∙
      (isoComp-cong (idIso (G ◁ δ)) ((preWhisker-comp-at α q r) ⁻¹) ∙
        (isoComp-assoc-at (G ◁ δ) (α ▷ (q ∘ r)) (comp-assoc r q F) ∙
          (isoComp-cong (interchange-at α δ) (idIso (comp-assoc r q F)) ∙
            (isoComp-assoc-at (α ▷ q′) (F ◁ δ) (comp-assoc r q F)) ⁻¹)))

module ApplicationInputRestriction {R Γ X C D : CAT}
  (F : MAP X (Map C D)) (p : MAP Γ X) (x : MAP Γ C) (r : MAP R Γ)
  (p′ : MAP R X) (δ : (p ∘ r) =₁ p′) where

  point = pair p x
  pointChange = pair-cong δ (idIso (x ∘ r)) ∙ pair-pre p x r
  mappingChange = (F ◁ δ) ∙ comp-assoc r p F
  left = mapUncurry-at F p x
  left′ = mapUncurry-at F p′ (x ∘ r)
  sourceChange = (mapUncurry F ◁ pointChange) ∙ comp-assoc r point (mapUncurry F)
  leftOutput = applyTerm-cong mappingChange (idIso (x ∘ r)) ∙ applyTerm-pre (F ∘ p) x r
  abstract
    comparison : (left′ ∙ sourceChange) =₂ (leftOutput ∙ (left ▷ r))
    comparison =
      let changed = pair-cong δ (idIso (x ∘ r))
          pairPre = pair-pre p x r
          middle = mapUncurry-at F (p ∘ r) (x ∘ r)
          A = comp-assoc r point (mapUncurry F)
          firstAction = applyTerm-cong (F ◁ δ) (idIso (x ∘ r))
          secondAction = applyTerm-cong (comp-assoc r p F) (idIso (x ∘ r))
          applicationPre = applyTerm-pre (F ∘ p) x r
          tail = (mapUncurry F ◁ pairPre) ∙ A
          normalizeAction : (firstAction ∙ secondAction) =₂
            (applyTerm-cong (mappingChange) (idIso (x ∘ r)))
          normalizeAction = apply-cong-Iso₂ (idIso (mappingChange))
              (isoComp-unitˡ-at (idIso (x ∘ r))) ∙
            (apply-cong-comp (F ◁ δ) (comp-assoc r p F)
              (idIso (x ∘ r)) (idIso (x ∘ r))) ⁻¹
          restriction : (middle ∙ tail) =₂ (secondAction ∙ (applicationPre ∙ (left ▷ r)))
          restriction = (mapUncurry-at-restriction F p x r) ⁻¹
          normalizeEnd : (firstAction ∙ (secondAction ∙ (applicationPre ∙ (left ▷ r)))) =₂
            (leftOutput ∙ (left ▷ r))
          normalizeEnd = (isoComp-assoc-at
              (applyTerm-cong (mappingChange) (idIso (x ∘ r))) applicationPre (left ▷ r)) ⁻¹ ∙
            (isoComp-cong normalizeAction (idIso (applicationPre ∙ (left ▷ r))) ∙
              (isoComp-assoc-at firstAction secondAction (applicationPre ∙ (left ▷ r))) ⁻¹)
          useRestriction : ((firstAction ∙ middle) ∙ tail) =₂
            (firstAction ∙ (secondAction ∙ (applicationPre ∙ (left ▷ r))))
          useRestriction = isoComp-cong (idIso firstAction) restriction ∙
            isoComp-assoc-at firstAction middle ((mapUncurry F ◁ pairPre) ∙ A)
          useChange : (left′ ∙ ((mapUncurry F ◁ changed) ∙ tail)) =₂
            ((firstAction ∙ middle) ∙ tail)
          useChange = isoComp-cong
              (mapUncurry-at-inner F δ (idIso (x ∘ r)))
              (idIso ((mapUncurry F ◁ pairPre) ∙ A)) ∙
            (isoComp-assoc-at left′ (mapUncurry F ◁ changed)
              ((mapUncurry F ◁ pairPre) ∙ A)) ⁻¹
          expand : (left′ ∙ sourceChange) =₂
            (left′ ∙ ((mapUncurry F ◁ changed) ∙ tail))
          expand = isoComp-cong (idIso left′)
            (isoComp-assoc-at (mapUncurry F ◁ changed) (mapUncurry F ◁ pairPre) A ∙
              isoComp-cong (postWhisker-isoComp-at (mapUncurry F) changed pairPre) (idIso A))
      in normalizeEnd ∙ (useRestriction ∙ (useChange ∙ expand))

```