# Composition and change of parameter

The comparison for applying a mapping term commutes with iterated
substitution. We retain the chosen pairing comparisons and the external
associator in this calculation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section03.ProductAssociativity as ProductAssociativity
import SCT.VolumeI.Chapter01.Section03.CompositionNaturality as CompositionNaturality
import SCT.VolumeI.Chapter01.Section03.EvaluationParameterChange as EvaluationParameterChange
import SCT.VolumeI.Chapter01.Section03.Currying as Currying
import SCT.VolumeI.Chapter01.Section03.InternalCoherence as InternalCoherence
import SCT.VolumeI.Chapter01.Section03.ParameterChange as ParameterChange
import SCT.VolumeI.Chapter01.Section03.ProductSubstitution as ProductSubstitution
import SCT.VolumeI.Chapter01.Section02.Structural as Structural
import SCT.VolumeI.Chapter01.Section02.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section02.ProductFunctorUnits as ProductFunctorUnits
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section02.IteratedPairing as IteratedPairing

module SCT.VolumeI.Chapter01.Section03.CompositionRestrictionCalculus
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open MapComposition 𝒯 M
open CompositionNaturality 𝒯 M
  using (coordinate-at)

open Currying 𝒯 M hiding (mapUncurryIso-at)
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

open import SCT.VolumeI.Chapter01.Section03.ApplicationRestriction 𝒯 M public
  hiding (combine-apply; post-iterated-comparison)
open import SCT.VolumeI.Chapter01.Section03.MappingProofCalculus 𝒯 M public

abstract
  binary-pre-substitution : {X Y A B C : CAT} (F : MAP (A × B) C)
    (f : MAP X A) (g : MAP X B) {r s : MAP Y X} (γ : =₁ r s)
    → let before = (F ◁ pair-pre f g r) ∙ comp-assoc r (pair f g) F
          after = (F ◁ pair-pre f g s) ∙ comp-assoc s (pair f g) F
      in =₂ (after ∙ ((F ∘ pair f g) ◁ γ))
          ((F ◁ pair-cong (f ◁ γ) (g ◁ γ)) ∙ before)
  binary-pre-substitution = CompositionNaturality.binary-pre-substitution 𝒯 M

abstract
  apply-compose-natural : {Γ C D E : CAT}
    {g g′ : MAP Γ (Map D E)} {f f′ : MAP Γ (Map C D)} {x x′ : MAP Γ C}
    (α : =₁ g g′) (β : =₁ f f′) (τ : =₁ x x′)
    → =₂ (apply-compose g′ f′ x′ ∙ applyTerm-cong (composeTerm-cong α β) τ)
        (applyTerm-cong α (applyTerm-cong β τ) ∙ apply-compose g f x)
  apply-compose-natural = CompositionNaturality.apply-compose-natural 𝒯 M

```
```agda
module BinaryOperation {A B Z : CAT} (F : MAP (A × B) Z) where
  term : {X : CAT} → MAP X A → MAP X B → MAP X Z
  term f x = F ∘ pair f x

  act : {X : CAT} {f g : MAP X A} {x y : MAP X B}
    → =₁ f g → =₁ x y → =₁ (term f x) (term g y)
  act α β = F ◁ pair-cong α β

  pre : {X Y : CAT} (f : MAP X A) (x : MAP X B) (r : MAP Y X)
    → =₁ (term f x ∘ r) (term (f ∘ r) (x ∘ r))
  pre f x r = (F ◁ pair-pre f x r) ∙ comp-assoc r (pair f x) F

  abstract
    act-comp : {X : CAT} {f₀ f₁ f₂ : MAP X A} {x₀ x₁ x₂ : MAP X B}
      (α₂ : =₁ f₁ f₂) (α₁ : =₁ f₀ f₁)
      (β₂ : =₁ x₁ x₂) (β₁ : =₁ x₀ x₁)
      → =₂ (act (α₂ ∙ α₁) (β₂ ∙ β₁)) (act α₂ β₂ ∙ act α₁ β₁)
    act-comp α₂ α₁ β₂ β₁ = postWhisker-isoComp-at F (pair-cong α₂ β₂) (pair-cong α₁ β₁) ∙
      (postWhisker F ◁ pair-cong-comp α₂ α₁ β₂ β₁)

  abstract
    act-Iso₂ : {X : CAT} {f g : MAP X A} {x y : MAP X B}
      {α α′ : =₁ f g} {β β′ : =₁ x y}
      → =₂ α α′ → =₂ β β′ → =₂ (act α β) (act α′ β′)
    act-Iso₂ p q = postWhisker F ◁ pair-cong-Iso₂ p q

  abstract
    act-id : {X : CAT} (f : MAP X A) (x : MAP X B)
      → =₂ (act (idIso f) (idIso x)) (idIso (term f x))
    act-id f x = postWhisker-idIso F (pair f x) ∙ (postWhisker F ◁ pair-cong-id f x)

  abstract
    combine : {X : CAT} {f₀ f₁ f₂ : MAP X A} {x₀ x₁ x₂ : MAP X B} {source : MAP X Z}
      (α : =₁ f₁ f₂) (β : =₁ x₁ x₂) (γ : =₁ f₀ f₁) (δ : =₁ x₀ x₁)
      (base : =₁ source (term f₀ x₀))
      → =₂ (act α β ∙ (act γ δ ∙ base)) (act (α ∙ γ) (β ∙ δ) ∙ base)
    combine α β γ δ base = isoComp-cong (invIso (act-comp α γ β δ)) (idIso base) ∙
      invIso (isoComp-assoc-at (act α β) (act γ δ) base)

  module Assembly {R Γ X : CAT}
    (H : MAP X A) (K : MAP X B)
    (q : MAP Γ X) (r : MAP R Γ) (q′ : MAP R X) (δ : =₁ (q ∘ r) q′)
    {f : MAP Γ A} {x : MAP Γ B}
    {f′ : MAP R A} {x′ : MAP R B}
    (a : =₁ (H ∘ q) f) (b : =₁ (K ∘ q) x)
    (a′ : =₁ (H ∘ q′) f′) (b′ : =₁ (K ∘ q′) x′)
    (c : =₁ (f ∘ r) f′) (d : =₁ (x ∘ r) x′) where
  
    normalization = act a b ∙ pre H K q
    normalization′ = act a′ b′ ∙ pre H K q′
  
    short = normalization′ ∙ ((term H K ◁ δ) ∙ comp-assoc r q (term H K))
    long = act c d ∙ (pre f x r ∙ (normalization ▷ r))
  
    base = pre (H ∘ q) (K ∘ q) r ∙ (pre H K q ▷ r)
  
    abstract
      short-normalization : =₂ short
        (act (a′ ∙ ((H ◁ δ) ∙ comp-assoc r q H))
          (b′ ∙ ((K ◁ δ) ∙ comp-assoc r q K)) ∙ base)
      short-normalization =
        let paired = act a′ b′
            changed = act (H ◁ δ) (K ◁ δ)
            A = comp-assoc r q (term H K)
            substitute = isoComp-assoc-at changed (pre H K (q ∘ r)) A ∙
              (isoComp-cong (binary-pre-substitution F H K δ) (idIso A) ∙
                invIso (isoComp-assoc-at (pre H K q′) (term H K ◁ δ) A))
            iterate = isoComp-cong (idIso changed) (binary-pre-iterated F H K q r)
            combineInner = combine (H ◁ δ) (K ◁ δ)
              (comp-assoc r q H) (comp-assoc r q K) base
        in combine a′ b′ ((H ◁ δ) ∙ comp-assoc r q H) ((K ◁ δ) ∙ comp-assoc r q K) base ∙
          (isoComp-cong (idIso paired) (combineInner ∙ (iterate ∙ substitute)) ∙
            isoComp-assoc-at paired (pre H K q′) ((term H K ◁ δ) ∙ A))
  
    abstract
      long-normalization : =₂ long
        (act (c ∙ (a ▷ r)) (d ∙ (b ▷ r)) ∙ base)
      long-normalization =
        let outer = act c d
            before = pre H K q ▷ r
            middle = pre f x r
            input = act a b ▷ r
            output = act (a ▷ r) (b ▷ r)
            exchange = isoComp-assoc-at output (pre (H ∘ q) (K ∘ q) r) before ∙
              (isoComp-cong (binary-pre-inputs F a b r) (idIso before) ∙
                invIso (isoComp-assoc-at middle input before))
        in combine c d (a ▷ r) (b ▷ r) base ∙
          (isoComp-cong (idIso outer) exchange ∙
            isoComp-cong (idIso outer) (isoComp-cong (idIso middle)
              (preWhisker-isoComp-at (act a b) (pre H K q) r)))
  
    abstract
      assemble :
        =₂ (a′ ∙ ((H ◁ δ) ∙ comp-assoc r q H)) (c ∙ (a ▷ r))
        → =₂ (b′ ∙ ((K ◁ δ) ∙ comp-assoc r q K)) (d ∙ (b ▷ r))
        → =₂ short long
      assemble first second = invIso long-normalization ∙
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
  N′ = act (invIso Ag) (invIso Af) ∙ pre g f (σ ∘ pr₁ {Q} {C})
  tail = (term g f ◁ δ) ∙ comp-assoc s pr₁ (term g f)
  T = pre (g ∘ σ) (f ∘ σ) (pr₁ {Q} {C}) ∙ (pre g f σ ▷ pr₁ {Q} {C})

  abstract
    old-normalization : =₂ N (pre g f pr₁)
    old-normalization = isoComp-unitˡ-at (pre g f pr₁) ∙
      isoComp-cong (act-id (g ∘ pr₁) (f ∘ pr₁)) (idIso (pre g f pr₁))

  abstract
    new-normalization : =₂ N′ (T ∙ invIso AB)
    new-normalization =
      let inverseAction = act (invIso Ag) (invIso Af)
          forwardAction = act Ag Af
          cancelAction = act-id ((g ∘ σ) ∘ pr₁) ((f ∘ σ) ∘ pr₁) ∙
            (act-Iso₂ (isoComp-inverseˡ-at Ag) (isoComp-inverseˡ-at Af) ∙
              invIso (act-comp (invIso Ag) Ag (invIso Af) Af))
          square = isoComp-unitˡ-at T ∙
            (isoComp-cong cancelAction (idIso T) ∙
              (invIso (isoComp-assoc-at inverseAction forwardAction T) ∙
                (isoComp-cong (idIso inverseAction) (binary-pre-iterated F g f σ pr₁) ∙
                  isoComp-assoc-at inverseAction (pre g f (σ ∘ pr₁)) AB)))
      in isoComp-cong square (idIso (invIso AB)) ∙ invIso (cancel-right AB N′)

  abstract
    compatibility : =₂
      (pre (g ∘ σ) (f ∘ σ) pr₁ ∙ ((pre g f σ ▷ pr₁) ∙ cB))
      (act cg cf ∙ (pre (g ∘ pr₁) (f ∘ pr₁) s ∙ (pre g f pr₁ ▷ s)))
    compatibility =
      let first = invIso (isoComp-unitʳ-at cg ∙
            isoComp-cong (idIso cg) (preWhisker-idIso (g ∘ pr₁) s))
          second = invIso (isoComp-unitʳ-at cf ∙
            isoComp-cong (idIso cf) (preWhisker-idIso (f ∘ pr₁) s))
          assembled = Assembly.assemble g f pr₁ s (σ ∘ pr₁) δ
            (idIso (g ∘ pr₁)) (idIso (f ∘ pr₁)) (invIso Ag) (invIso Af) cg cf first second
          left = isoComp-cong (invIso new-normalization) (idIso tail) ∙
            (invIso (isoComp-assoc-at T (invIso AB) tail) ∙
              invIso (isoComp-assoc-at (pre (g ∘ σ) (f ∘ σ) pr₁) (pre g f σ ▷ pr₁) cB))
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
    → =₂ (applyTerm-cong (idIso f) (idIso x)) (idIso (applyTerm f x))
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
    firstProjection : =₂
      (pair-β₁ (pair (g ∘ r) (f ∘ r)) (x ∘ r) ∙ (pr₁ ◁ pointChange))
      (pairChange ∙ ((pair-β₁ (pair g f) x ▷ r) ∙ invIso (comp-assoc r point pr₁)))
    firstProjection = pair-pre-cong-triangle₁ (pair g f) x r pairChange (idIso (x ∘ r))

    secondProjection : =₂
      (third′ ∙ (pr₂ ◁ pointChange))
      (idIso (x ∘ r) ∙ ((third ▷ r) ∙ invIso (comp-assoc r point pr₂)))
    secondProjection = pair-pre-cong-triangle₂ (pair g f) x r pairChange (idIso (x ∘ r))

  abstract
    third-restriction : =₂
      (third′ ∙ ((pr₂ ◁ pointChange) ∙ comp-assoc r point pr₂)) (third ▷ r)
    third-restriction = isoComp-unitˡ-at (third ▷ r) ∙
      projection-square-forward pr₂ point r point′ pointChange third third′ (idIso (x ∘ r))
        secondProjection

  abstract
    nested-projection : {A : CAT} (π : MAP (Map D E × Map C D) A)
      {v : MAP Γ A} (b : =₁ (π ∘ pair g f) v)
      (b′ : =₁ (π ∘ pair (g ∘ r) (f ∘ r)) (v ∘ r))
      → =₂ (b′ ∙ (π ◁ pairChange))
          ((b ▷ r) ∙ invIso (comp-assoc r (pair g f) π))
      → =₂
        ((b′ ∙ coordinate-at π pr₁ point′ (pair-β₁ (pair (g ∘ r) (f ∘ r)) (x ∘ r))) ∙
          (((π ∘ pr₁) ◁ pointChange) ∙ comp-assoc r point (π ∘ pr₁)))
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
              (idIso (v ∘ r)) (invIso (isoComp-unitˡ-at _) ∙ triangle)
          rearrange = invIso (isoComp-assoc-at b′ ((π ◁ pairChange) ∙ A) (old ▷ r)) ∙
            isoComp-cong (idIso b′) (invIso (isoComp-assoc-at (π ◁ pairChange) A (old ▷ r)))
      in invIso (preWhisker-isoComp-at b old r) ∙
        (isoComp-cong projection (idIso (old ▷ r)) ∙
          (rearrange ∙ (isoComp-cong (idIso b′) coordinate ∙ isoComp-assoc-at b′ new tail)))

  abstract
    first-restriction : =₂
      (first′ ∙ (((pr₁ ∘ pr₁) ◁ pointChange) ∙ comp-assoc r point (pr₁ ∘ pr₁)))
      (first ▷ r)
    first-restriction = nested-projection pr₁ (pair-β₁ g f) (pair-β₁ (g ∘ r) (f ∘ r))
      (pair-pre-triangle₁ g f r)

    second-restriction : =₂
      (second′ ∙ (((pr₂ ∘ pr₁) ◁ pointChange) ∙ comp-assoc r point (pr₂ ∘ pr₁)))
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
    inner-restriction : =₂
      (inner′ ∙ ((applyTerm (pr₂ ∘ pr₁) pr₂ ◁ pointChange) ∙
        comp-assoc r point (applyTerm (pr₂ ∘ pr₁) pr₂)))
      (applyTerm-pre f x r ∙ (inner ▷ r))
    inner-restriction = isoComp-unitˡ-at (applyTerm-pre f x r ∙ (inner ▷ r)) ∙
      (isoComp-cong (apply-identity-action (f ∘ r) (x ∘ r)) (idIso _) ∙
        ApplicationAssembly.assemble (pr₂ ∘ pr₁) pr₂ point r point′ pointChange
          second third second′ third′ (idIso (f ∘ r)) (idIso (x ∘ r))
          (invIso (isoComp-unitˡ-at (second ▷ r)) ∙ second-restriction)
          (invIso (isoComp-unitˡ-at (third ▷ r)) ∙ third-restriction))

  abstract
    outer-restriction : =₂
      (outer′ ∙ ((doubleEvaluation ◁ pointChange) ∙ comp-assoc r point doubleEvaluation))
      (applyTerm-cong (idIso (g ∘ r)) (applyTerm-pre f x r) ∙
        (applyTerm-pre g (applyTerm f x) r ∙ (outer ▷ r)))
    outer-restriction = ApplicationAssembly.assemble
      (pr₁ ∘ pr₁) (applyTerm (pr₂ ∘ pr₁) pr₂) point r point′ pointChange
      first inner first′ inner′ (idIso (g ∘ r)) (applyTerm-pre f x r)
      (invIso (isoComp-unitˡ-at (first ▷ r)) ∙ first-restriction) inner-restriction
```

```agda
abstract
  comparison-restriction : {R Γ X Y : CAT} {F G : MAP X Y}
    (α : =₁ F G) (q : MAP Γ X) (r : MAP R Γ) (q′ : MAP R X)
    (δ : =₁ (q ∘ r) q′)
    → =₂ ((α ▷ q′) ∙ ((F ◁ δ) ∙ comp-assoc r q F))
        (((G ◁ δ) ∙ comp-assoc r q G) ∙ ((α ▷ q) ▷ r))
  comparison-restriction {F = F} {G} α q r q′ δ =
    invIso (isoComp-assoc-at (G ◁ δ) (comp-assoc r q G) ((α ▷ q) ▷ r)) ∙
      (isoComp-cong (idIso (G ◁ δ)) (invIso (preWhisker-comp-at α q r)) ∙
        (isoComp-assoc-at (G ◁ δ) (α ▷ (q ∘ r)) (comp-assoc r q F) ∙
          (isoComp-cong (interchange-at α δ) (idIso (comp-assoc r q F)) ∙
            invIso (isoComp-assoc-at (α ▷ q′) (F ◁ δ) (comp-assoc r q F)))))

module ApplicationInputRestriction {R Γ X C D : CAT}
  (F : MAP X (Map C D)) (p : MAP Γ X) (x : MAP Γ C) (r : MAP R Γ)
  (p′ : MAP R X) (δ : =₁ (p ∘ r) p′) where

  point = pair p x
  pointChange = pair-cong δ (idIso (x ∘ r)) ∙ pair-pre p x r
  mappingChange = (F ◁ δ) ∙ comp-assoc r p F
  left = mapUncurry-at F p x
  left′ = mapUncurry-at F p′ (x ∘ r)
  sourceChange = (mapUncurry F ◁ pointChange) ∙ comp-assoc r point (mapUncurry F)
  leftOutput = applyTerm-cong mappingChange (idIso (x ∘ r)) ∙ applyTerm-pre (F ∘ p) x r
  abstract
    comparison : =₂ (left′ ∙ sourceChange) (leftOutput ∙ (left ▷ r))
    comparison =
      let changed = pair-cong δ (idIso (x ∘ r))
          pairPre = pair-pre p x r
          middle = mapUncurry-at F (p ∘ r) (x ∘ r)
          A = comp-assoc r point (mapUncurry F)
          firstAction = applyTerm-cong (F ◁ δ) (idIso (x ∘ r))
          secondAction = applyTerm-cong (comp-assoc r p F) (idIso (x ∘ r))
          applicationPre = applyTerm-pre (F ∘ p) x r
          tail = (mapUncurry F ◁ pairPre) ∙ A
          normalizeAction : =₂ (firstAction ∙ secondAction)
            (applyTerm-cong (mappingChange) (idIso (x ∘ r)))
          normalizeAction = apply-cong-Iso₂ (idIso (mappingChange))
              (isoComp-unitˡ-at (idIso (x ∘ r))) ∙
            invIso (apply-cong-comp (F ◁ δ) (comp-assoc r p F)
              (idIso (x ∘ r)) (idIso (x ∘ r)))
          restriction : =₂ (middle ∙ tail) (secondAction ∙ (applicationPre ∙ (left ▷ r)))
          restriction = invIso (mapUncurry-at-restriction F p x r)
          normalizeEnd : =₂ (firstAction ∙ (secondAction ∙ (applicationPre ∙ (left ▷ r))))
            (leftOutput ∙ (left ▷ r))
          normalizeEnd = invIso (isoComp-assoc-at
              (applyTerm-cong (mappingChange) (idIso (x ∘ r))) applicationPre (left ▷ r)) ∙
            (isoComp-cong normalizeAction (idIso (applicationPre ∙ (left ▷ r))) ∙
              invIso (isoComp-assoc-at firstAction secondAction (applicationPre ∙ (left ▷ r))))
          useRestriction : =₂ ((firstAction ∙ middle) ∙ tail)
            (firstAction ∙ (secondAction ∙ (applicationPre ∙ (left ▷ r))))
          useRestriction = isoComp-cong (idIso firstAction) restriction ∙
            isoComp-assoc-at firstAction middle ((mapUncurry F ◁ pairPre) ∙ A)
          useChange : =₂ (left′ ∙ ((mapUncurry F ◁ changed) ∙ tail))
            ((firstAction ∙ middle) ∙ tail)
          useChange = isoComp-cong
              (mapUncurry-at-inner F δ (idIso (x ∘ r)))
              (idIso ((mapUncurry F ◁ pairPre) ∙ A)) ∙
            invIso (isoComp-assoc-at left′ (mapUncurry F ◁ changed)
              ((mapUncurry F ◁ pairPre) ∙ A))
          expand : =₂ (left′ ∙ sourceChange)
            (left′ ∙ ((mapUncurry F ◁ changed) ∙ tail))
          expand = isoComp-cong (idIso left′)
            (isoComp-assoc-at (mapUncurry F ◁ changed) (mapUncurry F ◁ pairPre) A ∙
              isoComp-cong (postWhisker-isoComp-at (mapUncurry F) changed pairPre) (idIso A))
      in normalizeEnd ∙ (useRestriction ∙ (useChange ∙ expand))

```