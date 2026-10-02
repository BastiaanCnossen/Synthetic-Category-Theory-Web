# Equivalences assembled from family operations

An equivalence of endpoint families includes the two specified comparisons
and their inverse equations. Transport along these comparisons gives inverse
operations on framed expressions. Equivalences of operations compose using
their comparison actions and inverse equations; no law preserving composition
of comparisons is needed.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFamilyEquivalences
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFamilies 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameSquares 𝒯 M ℱ I
  using (cancel-frames)

record EndpointEquivalence {B C : CAT} (u v : EndpointFamily B C) : Set (c ⊔ m) where
  field
    forward : EndpointComparison u v
    backward : EndpointComparison v u
    backward-forward : {Γ : CAT} (b : MAP Γ B) →
      (EndpointComparison.component backward b ∙ EndpointComparison.component forward b)
        =₂ idIso (EndpointFamily.value u b)
    forward-backward : {Γ : CAT} (b : MAP Γ B) →
      (EndpointComparison.component forward b ∙ EndpointComparison.component backward b)
        =₂ idIso (EndpointFamily.value v b)

identity-endpoint-equivalence : {B C : CAT} (u : EndpointFamily B C) → EndpointEquivalence u u
identity-endpoint-equivalence u = record
  { forward = identity-comparison u ; backward = identity-comparison u
  ; backward-forward = λ b → isoComp-unitˡ-at (idIso (EndpointFamily.value u b))
  ; forward-backward = λ b → isoComp-unitˡ-at (idIso (EndpointFamily.value u b)) }

comparison-equivalence : {B C : CAT} {u v : EndpointFamily B C} →
  EndpointComparison u v → EndpointEquivalence u v
comparison-equivalence {u = u} {v} p = record
  { forward = p ; backward = inverse-comparison {u = u} {v = v} p
  ; backward-forward = λ b → isoComp-inverseˡ-at (EndpointComparison.component p b)
  ; forward-backward = λ b → isoComp-inverseʳ-at (EndpointComparison.component p b) }

record FamilyEquivalence {B C D : CAT} (u v : EndpointFamily B C)
  (s t : EndpointFamily B D) : Set (c ⊔ m) where
  field
    forward : FamilyOperation u v s t
    backward : FamilyOperation s t u v
    backward-forward : {Γ : CAT} (b : MAP Γ B) (f : Expressions.At u v b) →
      ExpressionIso (FamilyOperation.apply backward b (FamilyOperation.apply forward b f)) f
    forward-backward : {Γ : CAT} (b : MAP Γ B) (g : Expressions.At s t b) →
      ExpressionIso (FamilyOperation.apply forward b (FamilyOperation.apply backward b g)) g

inverse-family-equivalence : {B C D : CAT} {u v : EndpointFamily B C}
  {s t : EndpointFamily B D} → FamilyEquivalence u v s t → FamilyEquivalence s t u v
inverse-family-equivalence e = record
  { forward = E.backward ; backward = E.forward
  ; backward-forward = E.forward-backward ; forward-backward = E.backward-forward }
  where module E = FamilyEquivalence e

compose-family-equivalences : {B C D E : CAT} {u v : EndpointFamily B C}
  {s t : EndpointFamily B D} {x y : EndpointFamily B E} →
  FamilyEquivalence s t x y → FamilyEquivalence u v s t → FamilyEquivalence u v x y
compose-family-equivalences outer inner = record
  { forward = compose-operations G.forward F.forward
  ; backward = compose-operations F.backward G.backward
  ; backward-forward = λ b f → expressionIso-compose (F.backward-forward b f)
      (FamilyOperation.on-comparison F.backward b
        (G.backward-forward b (FamilyOperation.apply F.forward b f)))
  ; forward-backward = λ b g → expressionIso-compose (G.forward-backward b g)
      (FamilyOperation.on-comparison G.forward b
        (F.forward-backward b (FamilyOperation.apply G.backward b g))) }
  where
  module F = FamilyEquivalence inner
  module G = FamilyEquivalence outer

transport-family-equivalence : {B C : CAT} {u v s t : EndpointFamily B C} →
  EndpointEquivalence u s → EndpointEquivalence v t → FamilyEquivalence u v s t
transport-family-equivalence {u = u} {v} {s} {t} p q = record
  { forward = transport {u = u} {v = v} {s = s} {t = t} P.forward Q.forward
  ; backward = transport {u = s} {v = t} {s = u} {t = v} P.backward Q.backward
  ; backward-forward = λ b f → cancel-frames f
      (EndpointComparison.component P.forward b) (EndpointComparison.component Q.forward b)
      (EndpointComparison.component P.backward b) (EndpointComparison.component Q.backward b)
      (P.backward-forward b) (Q.backward-forward b)
  ; forward-backward = λ b g → cancel-frames g
      (EndpointComparison.component P.backward b) (EndpointComparison.component Q.backward b)
      (EndpointComparison.component P.forward b) (EndpointComparison.component Q.forward b)
      (P.forward-backward b) (Q.forward-backward b) }
  where
  module P = EndpointEquivalence p
  module Q = EndpointEquivalence q
```

The identity endpoint equivalence deliberately uses identity comparisons in
both directions. Inverting its forward comparison would be another valid
choice, but would change the literal endpoint frames. The constructor accepts
the chosen inverse data rather than imposing that convention.
