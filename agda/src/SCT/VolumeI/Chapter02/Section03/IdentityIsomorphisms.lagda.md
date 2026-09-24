# Identity arrows are isomorphisms

For `con:Identity_Isomorphism_Functor`, take two constant triangles.
Their common edges agree, and both long edges are the constant identity
arrow. The two pullback factorizations construct `identityIso`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section03.IdentityIsomorphisms
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section03.Isomorphisms 𝒯 M ℱ P I E public
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section07.IsomorphismLifting 𝒯 M ℱ using (funIsoReflect; funIsoReflect-β)

constant-restriction-raw : {A B C : CAT} (f : MAP A B) →
  (funUncurry (funPre f ∘ constantDiagram B C)) =₁ (funUncurry (constantDiagram A C))
constant-restriction-raw {A} {B} {C} f =
  (funCurry-β pr₁) ⁻¹ ∙
    (comp-unitˡ pr₁ ∙ (pair-β₁ (id C ∘ pr₁) (f ∘ pr₂) ∙
      ((funCurry-β pr₁ ▷ productMap (id C) f) ∙
        funPre-uncurry f (constantDiagram B C))))

constant-restriction : {A B C : CAT} (f : MAP A B) →
  (funPre f ∘ constantDiagram B C) =₁ (constantDiagram A C)
constant-restriction f = funIsoReflect _ _ (constant-restriction-raw f)

constant-restriction-β : {A B C : CAT} (f : MAP A B) →
  (funUncurryIso (constant-restriction {C = C} f)) =₂ (constant-restriction-raw f)
constant-restriction-β f = funIsoReflect-β _ _ (constant-restriction-raw f)

module Identity (C : CAT) where
  triangle : MAP C (Triangles C)
  triangle = constantDiagram [2] C

  common-edge : Cone (edge₀ {C}) edge₂ C
  common-edge = record
    { left = triangle ; right = triangle
    ; match = (constant-restriction d₂) ⁻¹ ∙ constant-restriction d₀ }

  triangles : MAP C (InverseTriangles C)
  triangles = pullbackLift common-edge

  long-edge : (r : MAP (InverseTriangles C) (Triangles C)) →
    (r ∘ triangles) =₁ triangle → ((edge₁ ∘ r) ∘ triangles) =₁ identityArrow
  long-edge r β = constant-restriction d₁ ∙
    ((edge₁ ◁ β) ∙ comp-assoc triangles r edge₁)

  first-long : ((edge₁ ∘ pullback₁) ∘ triangles) =₁ identityArrow
  first-long = long-edge pullback₁ (pullbackLift-β₁ common-edge)

  second-long : ((edge₁ ∘ pullback₂) ∘ triangles) =₁ identityArrow
  second-long = long-edge pullback₂ (pullbackLift-β₂ common-edge)

  identity-pair : (inverseIdentityEdges C ∘ pair (id C) (id C)) =₁
    (pair (identityArrow {C}) identityArrow)
  identity-pair = pair-cong
    (comp-unitʳ identityArrow ∙ ((identityArrow ◁ pair-β₂ (id C) (id C)) ∙ comp-assoc _ pr₂ identityArrow))
    (comp-unitʳ identityArrow ∙ ((identityArrow ◁ pair-β₁ (id C) (id C)) ∙ comp-assoc _ pr₁ identityArrow)) ∙
    pair-pre (identityArrow ∘ pr₂) (identityArrow ∘ pr₁) (pair (id C) (id C))

  identities : Cone (inverseLongEdges C) (inverseIdentityEdges C) C
  identities = record
    { left = triangles ; right = pair (id C) (id C)
    ; match = identity-pair ⁻¹ ∙
        (pair-cong first-long second-long ∙ pair-pre (edge₁ ∘ pullback₁) (edge₁ ∘ pullback₂) triangles) }

identityIso : {C : CAT} → MAP C (Iso C)
identityIso {C} = pullbackLift (Identity.identities C)

identityIso-arrow : {C : CAT} → (isoArrow ∘ identityIso) =₁ (identityArrow {C})
identityIso-arrow {C} = constant-restriction d₀ ∙
  ((edge₀ ◁ pullbackLift-β₁ (Identity.common-edge C)) ∙
  (comp-assoc (Identity.triangles C) pullback₁ edge₀ ∙
    (((edge₀ ∘ pullback₁) ◁ pullbackLift-β₁ (Identity.identities C)) ∙
      comp-assoc identityIso isoTriangles (edge₀ ∘ pullback₁))))
```
