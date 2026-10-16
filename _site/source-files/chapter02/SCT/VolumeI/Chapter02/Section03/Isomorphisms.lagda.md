# The isomorphism category and identity isomorphisms

The isomorphism category is the specified iterated pullback of the two
inverse triangles. The common arrow is the second short edge of the first
triangle and the first short edge of the second. Their long edges are
identified with the two identity arrows in reversed object order.

Two constant triangles construct the identity-isomorphism functor. Both
pullback computation laws retain their complete matching squares. The arrow
and endpoint comparisons below refer to that actual chosen functor.
No Segal, composition-unit, associativity or Rezk assumption is used here.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section03.Isomorphisms where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (comp-unitˡ; comp-unitʳ; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section06.Cones using (Cone; ConeIdentification₁; cone-restrict)
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
  using (Pullback; pullback₁; pullback₂; pullback-cone; pullback-factor; pullback-factor-β)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (funEval; funUniversal)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPre; funPre-uncurry)
open import SCT.VolumeI.Chapter01.Section07.Currying using (funUncurry; reflect)
open import SCT.VolumeI.Chapter02.Section01.WalkingTriangle using ([2]; d₀; d₁; d₂)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (Ar; ev₀; ev₁; identityArrow; identity-source; identity-target;
    constantArrow; constantArrow-image)
open import SCT.VolumeI.Chapter02.Section01.HomAndSlices using (endpointMap)
open import SCT.VolumeI.Chapter02.Section01.Triangles using (Triangles; edge₀; edge₁; edge₂)

module _ {Γ : Context} where
  InverseTriangles : CAT Γ → CAT Γ
  InverseTriangles C = Pullback (edge₀ {C = C}) edge₂

  firstInverseTriangle : (C : CAT Γ) → MAP (InverseTriangles C) (Triangles C)
  firstInverseTriangle C = pullback₁ {f = edge₀ {C = C}} {g = edge₂}
  secondInverseTriangle : (C : CAT Γ) → MAP (InverseTriangles C) (Triangles C)
  secondInverseTriangle C = pullback₂ {f = edge₀ {C = C}} {g = edge₂}

  inverseLongEdges : (C : CAT Γ) → MAP (InverseTriangles C) (Ar C × Ar C)
  inverseLongEdges C = pair (edge₁ ∘ firstInverseTriangle C) (edge₁ ∘ secondInverseTriangle C)

  inverseIdentityEdges : (C : CAT Γ) → MAP (C × C) (Ar C × Ar C)
  inverseIdentityEdges C = pair (identityArrow ∘ pr₂) (identityArrow ∘ pr₁)

  Iso : CAT Γ → CAT Γ
  Iso C = Pullback (inverseLongEdges C) (inverseIdentityEdges C)

  isoTriangles : (C : CAT Γ) → MAP (Iso C) (InverseTriangles C)
  isoTriangles C = pullback₁ {f = inverseLongEdges C} {g = inverseIdentityEdges C}
  isoObjects : (C : CAT Γ) → MAP (Iso C) (C × C)
  isoObjects C = pullback₂ {f = inverseLongEdges C} {g = inverseIdentityEdges C}

  isoArrow : (C : CAT Γ) → MAP (Iso C) (Ar C)
  isoArrow C = (edge₀ ∘ firstInverseTriangle C) ∘ isoTriangles C

  isoEndpoints : (C : CAT Γ) → MAP (Iso C) (C × C)
  isoEndpoints C = endpointMap C ∘ isoArrow C
```

Restriction of a constant diagram is compared with the constant diagram
through the actual functor-category evaluation. This finite calculation
uses the existing constantArrow beta and native reflection.

```agda
  private
    constant-restriction-raw : {A B C : CAT Γ} (f : MAP A B) →
      funUncurry (funPre {D = C} f ∘ constantArrow B C) =₁
        funUncurry (constantArrow A C)
    constant-restriction-raw {A} {B} {C} f = (constantArrow-image A C) ⁻¹ ∙
      (comp-unitˡ pr₁ ∙
        (pair-β₁ (id C ∘ pr₁) (f ∘ pr₂) ∙
          ((constantArrow-image B C ▷ productMap (id C) f) ∙
            funPre-uncurry f (constantArrow B C))))

    constant-restriction : {A B C : CAT Γ} (f : MAP A B) →
      (funPre {D = C} f ∘ constantArrow B C) =₁ constantArrow A C
    constant-restriction {A} {B} {C} f = reflect (funEval {C = A} {D = C})
      (funUniversal A C) _ _ (constant-restriction-raw f)

  module Identity (C : CAT Γ) where
    triangle : MAP C (Triangles C)
    triangle = constantArrow [2] C

    common-edge : Cone (edge₀ {C = C}) edge₂ C
    common-edge = record
      { left = triangle; right = triangle
      ; match = (constant-restriction d₂) ⁻¹ ∙ constant-restriction d₀ }

    triangles : MAP C (InverseTriangles C)
    triangles = pullback-factor common-edge

    triangles-image : ConeIdentification₁
      (cone-restrict triangles (pullback-cone (edge₀ {C = C}) edge₂)) common-edge
    triangles-image = pullback-factor-β common-edge

    private
      long-edge : (r : MAP (InverseTriangles C) (Triangles C)) →
        (r ∘ triangles) =₁ triangle → ((edge₁ ∘ r) ∘ triangles) =₁ identityArrow
      long-edge r β = constant-restriction d₁ ∙
        ((edge₁ ◁ β) ∙ comp-assoc triangles r edge₁)

    first-long : ((edge₁ ∘ firstInverseTriangle C) ∘ triangles) =₁ identityArrow
    first-long = long-edge (firstInverseTriangle C) (ConeIdentification₁.left triangles-image)
    second-long : ((edge₁ ∘ secondInverseTriangle C) ∘ triangles) =₁ identityArrow
    second-long = long-edge (secondInverseTriangle C) (ConeIdentification₁.right triangles-image)

    private
      identity-pair : (inverseIdentityEdges C ∘ pair (id C) (id C)) =₁
        pair (identityArrow {C = C}) identityArrow
      identity-pair = pair⁼
        (comp-unitʳ identityArrow ∙
          ((identityArrow ◁ pair-β₂ (id C) (id C)) ∙
            comp-assoc (pair (id C) (id C)) pr₂ identityArrow))
        (comp-unitʳ identityArrow ∙
          ((identityArrow ◁ pair-β₁ (id C) (id C)) ∙
            comp-assoc (pair (id C) (id C)) pr₁ identityArrow)) ∙
          pair-pre (identityArrow ∘ pr₂) (identityArrow ∘ pr₁) (pair (id C) (id C))

    identities : Cone (inverseLongEdges C) (inverseIdentityEdges C) C
    identities = record
      { left = triangles; right = pair (id C) (id C)
      ; match = identity-pair ⁻¹ ∙
          (pair⁼ first-long second-long ∙
            pair-pre (edge₁ ∘ firstInverseTriangle C) (edge₁ ∘ secondInverseTriangle C) triangles) }

  identityIso : (C : CAT Γ) → MAP C (Iso C)
  identityIso C = pullback-factor (Identity.identities C)

  identityIso-image : (C : CAT Γ) → ConeIdentification₁
    (cone-restrict (identityIso C) (pullback-cone (inverseLongEdges C) (inverseIdentityEdges C)))
    (Identity.identities C)
  identityIso-image C = pullback-factor-β (Identity.identities C)

  identityIso-triangles : (C : CAT Γ) →
    (isoTriangles C ∘ identityIso C) =₁ Identity.triangles C
  identityIso-triangles C = ConeIdentification₁.left (identityIso-image C)
  identityIso-objects : (C : CAT Γ) →
    (isoObjects C ∘ identityIso C) =₁ pair (id C) (id C)
  identityIso-objects C = ConeIdentification₁.right (identityIso-image C)

  identityIso-arrow : (C : CAT Γ) →
    (isoArrow C ∘ identityIso C) =₁ identityArrow
  identityIso-arrow C = constant-restriction d₀ ∙
    ((edge₀ ◁ ConeIdentification₁.left (Identity.triangles-image C)) ∙
      (comp-assoc (Identity.triangles C) (firstInverseTriangle C) edge₀ ∙
        (((edge₀ ∘ firstInverseTriangle C) ◁ identityIso-triangles C) ∙
          comp-assoc (identityIso C) (isoTriangles C) (edge₀ ∘ firstInverseTriangle C))))

  identityIso-endpoints : (C : CAT Γ) →
    (isoEndpoints C ∘ identityIso C) =₁ pair (id C) (id C)
  identityIso-endpoints C = pair⁼ identity-source identity-target ∙
    (pair-pre ev₀ ev₁ identityArrow ∙
      ((endpointMap C ◁ identityIso-arrow C) ∙
        comp-assoc (identityIso C) (isoArrow C) (endpointMap C)))
```
