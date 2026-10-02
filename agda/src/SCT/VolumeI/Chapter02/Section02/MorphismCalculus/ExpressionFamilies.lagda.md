# Operations between specified endpoint families

Endpoint families separate endpoint formulas from their representing
pullbacks. A family supplies its restriction and parameter-change frames.
No laws comparing iterated restrictions or changes are assumed. Operations
carry only the finite compatibilities required by the existing realization.
An action on comparisons is part of these data; preservation of identities or
composition of comparisons is not assumed.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameSquares 𝒯 M ℱ I
  using (retarget-square; restrict-frame-square)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Pairing
open Pairing vocabulary terminal products productLaws composition vertical whiskering using (move-square)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse)

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I
  using (post-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (post-retarget; retarget-assoc)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestrictionFrames 𝒯 M ℱ I
  using (restrict-post-frames)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestriction 𝒯 M ℱ I
  using (restrict-expression-compose; restrict-expression-parameter)
open import SCT.VolumeI.Chapter01.Section04.Substitution.ConstantSubstitution 𝒯 M
  using (constant-image; constant-image-pre)

import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as Iterated
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.FunctorCoherence as EndpointUnits
open EndpointUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (left-unitor-comp)
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-comp-at; postWhisker-id-at)
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pentagon-whiskered)

record EndpointFamily (B C : CAT) : Set (c ⊔ m) where
  field
    value : {Γ : CAT} → MAP Γ B → MAP Γ C
    restriction : {Γ Δ : CAT} (b : MAP Γ B) (h : MAP Δ Γ) →
      (value b ∘ h) =₁ value (b ∘ h)
    change : {Γ : CAT} {b d : MAP Γ B} → b =₁ d → value b =₁ value d

module Expressions {B C : CAT} (u v : EndpointFamily B C) where
  private
    module U = EndpointFamily u
    module V = EndpointFamily v
  At : {Γ : CAT} → MAP Γ B → Set m
  At b = MorphismExpression (U.value b) (V.value b)

  restrict : {Γ Δ : CAT} (b : MAP Γ B) → At b → (h : MAP Δ Γ) → At (b ∘ h)
  restrict b f h = retarget-expression (restrict-expression f h) (U.restriction b h) (V.restriction b h)

  change : {Γ : CAT} {b d : MAP Γ B} → At b → b =₁ d → At d
  change f σ = retarget-expression f (U.change σ) (V.change σ)

record FamilyOperation {B C D : CAT} (u v : EndpointFamily B C)
  (s t : EndpointFamily B D) : Set (c ⊔ m) where
  private
    module Source = Expressions u v
    module Target = Expressions s t
  field
    apply : {Γ : CAT} (b : MAP Γ B) → Source.At b → Target.At b
    on-comparison : {Γ : CAT} (b : MAP Γ B) {f g : Source.At b} →
      ExpressionIso f g → ExpressionIso (apply b f) (apply b g)
    on-restriction : {Γ Δ : CAT} (b : MAP Γ B) (f : Source.At b) (h : MAP Δ Γ) →
      ExpressionIso (Target.restrict b (apply b f) h) (apply (b ∘ h) (Source.restrict b f h))
    on-change : {Γ : CAT} {b d : MAP Γ B} (f : Source.At b) (σ : b =₁ d) →
      ExpressionIso (Target.change (apply b f) σ) (apply d (Source.change f σ))

compose-operations : {B C D E : CAT} {u v : EndpointFamily B C}
  {s t : EndpointFamily B D} {x y : EndpointFamily B E} →
  FamilyOperation s t x y → FamilyOperation u v s t → FamilyOperation u v x y
compose-operations outer inner = record
  { apply = λ b f → G.apply b (F.apply b f)
  ; on-comparison = λ b Φ → G.on-comparison b (F.on-comparison b Φ)
  ; on-restriction = λ b f h → expressionIso-compose
      (G.on-comparison (b ∘ h) (F.on-restriction b f h))
      (G.on-restriction b (F.apply b f) h)
  ; on-change = λ { {b = b} {d} f σ → expressionIso-compose
      (G.on-comparison d (F.on-change f σ)) (G.on-change (F.apply b f) σ) }
  }
  where
  module F = FamilyOperation inner
  module G = FamilyOperation outer
```

Endpoint transport supplies two actual squares per endpoint. These squares
are mathematical input, not consequences inferred from arbitrary frames.
The constructor builds the full expression comparisons from them.

```agda
record EndpointComparison {B C : CAT} (u v : EndpointFamily B C) : Set (c ⊔ m) where
  private
    module U = EndpointFamily u
    module V = EndpointFamily v
  field
    component : {Γ : CAT} (b : MAP Γ B) → U.value b =₁ V.value b
    restriction-square : {Γ Δ : CAT} (b : MAP Γ B) (h : MAP Δ Γ) →
      (V.restriction b h ∙ (component b ▷ h)) =₂ (component (b ∘ h) ∙ U.restriction b h)
    change-square : {Γ : CAT} {b d : MAP Γ B} (σ : b =₁ d) →
      (V.change σ ∙ component b) =₂ (component d ∙ U.change σ)

transport : {B C : CAT} {u v s t : EndpointFamily B C} →
  EndpointComparison u s → EndpointComparison v t → FamilyOperation u v s t
transport {u = u} {v} {s} {t} p q = record
  { apply = λ b f → retarget-expression f (P.component b) (Q.component b)
  ; on-comparison = λ b Φ → retarget-expressionIso Φ (P.component b) (Q.component b)
  ; on-restriction = λ b f h → restrict-frame-square f (P.component b) (Q.component b) h
      (S.restriction b h) (T.restriction b h) (U.restriction b h) (V.restriction b h)
      (P.component (b ∘ h)) (Q.component (b ∘ h)) (P.restriction-square b h) (Q.restriction-square b h)
  ; on-change = λ { {b = b} {d} f σ → retarget-square f
      (P.component b) (Q.component b) (U.change σ) (V.change σ)
      (S.change σ) (T.change σ) (P.component d) (Q.component d)
      (P.change-square σ) (Q.change-square σ) }
  }
  where
  module U = EndpointFamily u
  module V = EndpointFamily v
  module S = EndpointFamily s
  module T = EndpointFamily t
  module P = EndpointComparison p
  module Q = EndpointComparison q

identity-comparison : {B C : CAT} (u : EndpointFamily B C) → EndpointComparison u u
identity-comparison u = record
  { component = λ b → idIso (U.value b)
  ; restriction-square = λ b h → (isoComp-unitˡ-at (U.restriction b h)) ⁻¹ ∙
      (isoComp-unitʳ-at (U.restriction b h) ∙
        isoComp-cong (idIso (U.restriction b h)) (preWhisker-idIso (U.value b) h))
  ; change-square = λ σ → (isoComp-unitˡ-at (U.change σ)) ⁻¹ ∙ isoComp-unitʳ-at (U.change σ) }
  where module U = EndpointFamily u

inverse-comparison : {B C : CAT} {u v : EndpointFamily B C} →
  EndpointComparison u v → EndpointComparison v u
inverse-comparison {u = u} {v} p = record
  { component = λ b → P.component b ⁻¹
  ; restriction-square = λ b h →
      (move-square (P.component (b ∘ h)) (U.restriction b h) (V.restriction b h)
        (P.component b ▷ h) ((P.restriction-square b h) ⁻¹)) ⁻¹ ∙
      isoComp-cong (idIso (U.restriction b h)) (pre-inverse (P.component b) h)
  ; change-square = λ { {b = b} {d} σ →
      (move-square (P.component d) (U.change σ) (V.change σ)
        (P.component b) ((P.change-square σ) ⁻¹)) ⁻¹ } }
  where
  module U = EndpointFamily u
  module V = EndpointFamily v
  module P = EndpointComparison p

represented : {B C : CAT} → MAP B C → EndpointFamily B C
represented u = record
  { value = λ b → u ∘ b
  ; restriction = λ b h → comp-assoc h b u
  ; change = λ σ → u ◁ σ }

post : {B C D : CAT} → MAP C D → EndpointFamily B C → EndpointFamily B D
post l u = record
  { value = λ b → l ∘ U.value b
  ; restriction = λ b h → (l ◁ U.restriction b h) ∙ comp-assoc h (U.value b) l
  ; change = λ σ → l ◁ U.change σ }
  where module U = EndpointFamily u

```

Postcomposition and constant families are basic examples. The constant-image
comparison supplies the two endpoint squares needed by transport; composition
then supplies the compatibility of the complete operation.

```agda
post-operation : {B C D : CAT} (F : MAP C D) (u v : EndpointFamily B C) →
  FamilyOperation u v (post F u) (post F v)
post-operation F u v = record
  { apply = λ b f → post-expression F f
  ; on-comparison = λ b Φ → post-expressionIso F Φ
  ; on-restriction = λ b f h → restrict-post-frames F f h
      (U.restriction b h) (V.restriction b h)
  ; on-change = λ f σ → expressionIso-inverse (post-retarget F f (U.change σ) (V.change σ)) }
  where
  module U = EndpointFamily u
  module V = EndpointFamily v

constant-family : {B C : CAT} → Obj-abs C → EndpointFamily B C
constant-family x = record
  { value = λ { {Γ} b → const {P = Γ} x }
  ; restriction = λ b h → const-pre x h
  ; change = λ σ → idIso (const x) }

private
  identity-square : {Γ C D : CAT} (F : MAP C D) (u : MAP Γ C)
    {v : MAP Γ D} (p : (F ∘ u) =₁ v) →
    (idIso v ∙ p) =₂ (p ∙ (F ◁ idIso u))
  identity-square F u p =
    (isoComp-cong (idIso p) (postWhisker-idIso F u)) ⁻¹ ∙
      ((isoComp-unitʳ-at p) ⁻¹ ∙ isoComp-unitˡ-at p)

constant-image-frame : {B C D : CAT} (F : MAP C D) (x : Obj-abs C) →
  EndpointComparison (post F (constant-family {B = B} x)) (constant-family (F ∘ x))
constant-image-frame F x = record
  { component = λ { {Γ} b → constant-image Γ F x }
  ; restriction-square = λ b h → constant-image-pre h F x
  ; change-square = λ { {Γ} σ → identity-square F (const {P = Γ} x) (constant-image Γ F x) } }

```

A represented composite and a postcomposed represented family have different
endpoint formulas. The associator compares them. Its restriction square is
the existing pentagon, and its change square is whiskering compatibility.

```agda
associator-frame : {B C D : CAT} (x : MAP B C) (l : MAP C D) →
  EndpointComparison (represented (l ∘ x)) (post l (represented x))
associator-frame x l = record
  { component = λ b → comp-assoc b x l
  ; restriction-square = λ b h →
      ((isoComp-assoc-at (l ◁ comp-assoc h b x) (comp-assoc h (x ∘ b) l)
        (comp-assoc b x l ▷ h)) ⁻¹ ∙ pentagon-whiskered h b x l) ⁻¹
  ; change-square = λ σ → (postWhisker-comp-at σ x l) ⁻¹ }

```

A variable endpoint is already a functor from the parameter category, so its
restriction and change require no composition. After postcomposition, its
endpoint formula agrees with the represented family. The identity comparison
below accounts for the different specified restriction frames.

```agda
variable-family : (C : CAT) → EndpointFamily C C
variable-family C = record
  { value = λ b → b
  ; restriction = λ b h → idIso (b ∘ h)
  ; change = λ σ → σ }

post-variable-frame : {C D : CAT} (F : MAP C D) →
  EndpointComparison (post F (variable-family C)) (represented F)
post-variable-frame F = record
  { component = λ b → idIso (F ∘ b)
  ; restriction-square = λ b h →
      (isoComp-unitˡ-at ((F ◁ idIso (b ∘ h)) ∙ comp-assoc h b F)) ⁻¹ ∙
      (isoComp-cong (postWhisker-idIso F (b ∘ h)) (idIso (comp-assoc h b F))) ⁻¹ ∙
      (isoComp-unitˡ-at (comp-assoc h b F)) ⁻¹ ∙
      isoComp-unitʳ-at (comp-assoc h b F) ∙
      isoComp-cong (idIso (comp-assoc h b F)) (preWhisker-idIso (F ∘ b) h)
  ; change-square = λ σ →
      (isoComp-unitˡ-at (F ◁ σ)) ⁻¹ ∙ isoComp-unitʳ-at (F ◁ σ) }
```

The left unitor compares a represented identity with a variable endpoint.
Its restriction and change squares are the existing unitor laws.

```agda
unit-frame : (C : CAT) → EndpointComparison (represented (id C)) (variable-family C)
unit-frame C = record
  { component = λ b → comp-unitˡ b
  ; restriction-square = λ b h →
      (left-unitor-comp h b) ⁻¹ ∙ isoComp-unitˡ-at (comp-unitˡ b ▷ h)
  ; change-square = λ σ → (postWhisker-id-at σ) ⁻¹ }
```

A section chooses an expression at each parameter, together with its two
finite compatibility comparisons. Restriction of one expression supplies a
section of represented endpoints. Applying a family operation transports a
section and supplies its comparisons without a new endpoint calculation.

```agda
record FamilySection {B C : CAT} (u v : EndpointFamily B C) : Set (c ⊔ m) where
  private module F = Expressions u v
  field
    at : {Γ : CAT} (b : MAP Γ B) → F.At b
    on-restriction : {Γ Δ : CAT} (b : MAP Γ B) (h : MAP Δ Γ) →
      ExpressionIso (F.restrict b (at b) h) (at (b ∘ h))
    on-change : {Γ : CAT} {b d : MAP Γ B} (σ : b =₁ d) →
      ExpressionIso (F.change (at b) σ) (at d)

restricted-section : {B C : CAT} {u v : MAP B C} →
  MorphismExpression u v → FamilySection (represented u) (represented v)
restricted-section f = record
  { at = λ b → restrict-expression f b
  ; on-restriction = λ b h → restrict-expression-compose f b h
  ; on-change = λ σ → restrict-expression-parameter f σ }

map-section : {B C D : CAT} {u v : EndpointFamily B C} {s t : EndpointFamily B D} →
  FamilyOperation u v s t → FamilySection u v → FamilySection s t
map-section operation section = record
  { at = λ b → O.apply b (F.at b)
  ; on-restriction = λ b h → expressionIso-compose
      (O.on-comparison (b ∘ h) (F.on-restriction b h))
      (O.on-restriction b (F.at b) h)
  ; on-change = λ { {b = b} {d} σ → expressionIso-compose
      (O.on-comparison d (F.on-change σ)) (O.on-change (F.at b) σ) } }
  where
  module O = FamilyOperation operation
  module F = FamilySection section

section-restrict-change : {B C : CAT} {u v : EndpointFamily B C}
  (section : FamilySection u v) {Γ Δ : CAT} (b : MAP Γ B) (h : MAP Δ Γ)
  {d : MAP Δ B} (σ : (b ∘ h) =₁ d) →
  ExpressionIso (retarget-expression (restrict-expression (FamilySection.at section b) h)
    (EndpointFamily.change u σ ∙ EndpointFamily.restriction u b h)
    (EndpointFamily.change v σ ∙ EndpointFamily.restriction v b h))
    (FamilySection.at section d)
section-restrict-change {u = u} {v} section b h σ = expressionIso-compose
  (F.on-change σ)
  (expressionIso-compose (retarget-expressionIso (F.on-restriction b h) (U.change σ) (V.change σ))
    (expressionIso-inverse (retarget-assoc (restrict-expression (F.at b) h)
      (U.restriction b h) (V.restriction b h) (U.change σ) (V.change σ))))
  where
  module U = EndpointFamily u
  module V = EndpointFamily v
  module F = FamilySection section
```
