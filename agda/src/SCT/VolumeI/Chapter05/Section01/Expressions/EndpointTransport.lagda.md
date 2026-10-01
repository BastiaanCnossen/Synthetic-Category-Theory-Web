# Transport between identification endpoints

The elementary endpoint-transport calculations follow from the finite vertical calculus. Their restricted assumptions keep the comparison syntax independent of mapping-anima constructors.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus as Inverses

module SCT.VolumeI.Chapter05.Section01.Expressions.EndpointTransport {l : Level} (T : Theory l l l) where
open View T
open Calculus T
open Inverses T using (inverse-composite)

-- The elementary part of canonical Section04.CoherenceTransport, kept in a
-- small module to avoid importing its broad Setup dependency.
-- These are proved from the same finite vertical calculus, not extra axioms.
changeEndpoints : {C D : CAT} {f f' g g' : MAP C D} → f =₁ f' → g =₁ g' → f =₁ g → f' =₁ g'
changeEndpoints p q alpha = q ∙ (alpha ∙ (p ⁻¹))

opaque
  changeEndpoints-boundaries : {C D : CAT} {f f' g g' : MAP C D}
    {p p' : f =₁ f'} {q q' : g =₁ g'} (alpha : f =₁ g)
    → p =₂ p' → q =₂ q' → changeEndpoints p q alpha =₂ changeEndpoints p' q' alpha
  changeEndpoints-boundaries alpha a b = isoComp-cong b (isoComp-cong (idIso alpha) (＝-inv ◁ a))

  changeEndpoints-successive : {C D : CAT} {f₀ f₁ f₂ g₀ g₁ g₂ : MAP C D}
    (p : f₀ =₁ f₁) (q : g₀ =₁ g₁) (r : f₁ =₁ f₂) (s : g₁ =₁ g₂)
    (alpha : f₀ =₁ g₀)
    → changeEndpoints r s (changeEndpoints p q alpha) =₂
      changeEndpoints (r ∙ p) (s ∙ q) alpha
  changeEndpoints-successive p q r s alpha =
    isoComp-cong (idIso s) (isoComp-assoc-at q (alpha ∙ p ⁻¹) (r ⁻¹)) then
    (isoComp-assoc-at s q ((alpha ∙ p ⁻¹) ∙ r ⁻¹)) ⁻¹ then
    isoComp-cong (idIso (s ∙ q))
      (isoComp-assoc-at alpha (p ⁻¹) (r ⁻¹) then
        isoComp-cong (idIso alpha) ((inverse-composite r p) ⁻¹))

  changeEndpoints-cong : {C D : CAT} {f f' g g' : MAP C D} (p : f =₁ f') (q : g =₁ g')
    {alpha beta : f =₁ g} → alpha =₂ beta → changeEndpoints p q alpha =₂ changeEndpoints p q beta
  changeEndpoints-cong p q r = isoComp-cong (idIso _) (isoComp-cong r (idIso _))

  cancel-inverse-pair : {C D : CAT} {f g h : MAP C D} (q : g =₁ h) (u : f =₁ g)
    → ((q ⁻¹) ∙ (q ∙ u)) =₂ u
  cancel-inverse-pair q u = (isoComp-assoc-at (q ⁻¹) q u) ⁻¹ then
    isoComp-cong (isoComp-inverseˡ-at q) (idIso _) then isoComp-unitˡ-at u

  changeEndpoints-comp : {C D : CAT} {f f' g g' h h' : MAP C D}
    (p : f =₁ f') (q : g =₁ g') (r : h =₁ h') (beta : g =₁ h) (alpha : f =₁ g)
    → (changeEndpoints q r beta ∙ changeEndpoints p q alpha) =₂ changeEndpoints p r (beta ∙ alpha)
  changeEndpoints-comp p q r beta alpha =
    isoComp-assoc-at r (beta ∙ (q ⁻¹)) (q ∙ (alpha ∙ (p ⁻¹))) then
    isoComp-cong (idIso _) (isoComp-assoc-at beta (q ⁻¹) (q ∙ (alpha ∙ (p ⁻¹))) then
      isoComp-cong (idIso _) (cancel-inverse-pair q (alpha ∙ (p ⁻¹))) then
      (isoComp-assoc-at beta alpha (p ⁻¹)) ⁻¹)

  changeEndpoints-id : {C D : CAT} {f g : MAP C D} (p : f =₁ g)
    → changeEndpoints p p (idIso f) =₂ idIso g
  changeEndpoints-id p = isoComp-cong (idIso _) (isoComp-unitˡ-at (p ⁻¹)) then isoComp-inverseʳ-at p

  square-to-changeEndpoints : {C D : CAT} {f f' g g' : MAP C D}
    (p : f =₁ f') (q : g =₁ g') (alpha : f =₁ g) (beta : f' =₁ g')
    → (q ∙ alpha) =₂ (beta ∙ p) → changeEndpoints p q alpha =₂ beta
  square-to-changeEndpoints p q alpha beta square = (isoComp-assoc-at q alpha (p ⁻¹)) ⁻¹ then
    isoComp-cong square (idIso _) then isoComp-assoc-at beta p (p ⁻¹) then
    isoComp-cong (idIso _) (isoComp-inverseʳ-at p) then isoComp-unitʳ-at beta

  changeEndpoints-to-square : {C D : CAT} {f f' g g' : MAP C D}
    (p : f =₁ f') (q : g =₁ g') (alpha : f =₁ g) (beta : f' =₁ g')
    → changeEndpoints p q alpha =₂ beta → (q ∙ alpha) =₂ (beta ∙ p)
  changeEndpoints-to-square p q alpha beta comparison =
    isoComp-cong (idIso _) ((isoComp-unitʳ-at alpha) ⁻¹ then
      isoComp-cong (idIso _) ((isoComp-inverseˡ-at p) ⁻¹) then (isoComp-assoc-at alpha (p ⁻¹) p) ⁻¹) then
    (isoComp-assoc-at q (alpha ∙ (p ⁻¹)) p) ⁻¹ then isoComp-cong comparison (idIso _)
```
