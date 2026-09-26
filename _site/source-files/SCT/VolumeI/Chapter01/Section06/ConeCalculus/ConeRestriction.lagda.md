# Restricting cone comparisons

Restriction uses the associators specified in `conePre`. The matching
square is transported by prewhiskering and the mixed whiskering law.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PairingUnits
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as IteratedPairing

module SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.Comparisons 𝒯 public
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (pre-square-projection)
open PairingUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (unit-square-projection; right-unitor-comp)
open Structural vocabulary terminal products productLaws composition whiskering using (whisker-mixed-at)
open IteratedPairing vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (transport-pre; transport-pre-assoc; pentagon-whiskered)

coneIso-pre : {C D E S T : CAT} {f : MAP C E} {g : MAP D E}
  {s t : Cone f g T} (r : MAP S T) → ConeIso s t → ConeIso (conePre r s) (conePre r t)
coneIso-pre {f = f} {g} {s} {t} r Φ = record
  { leftIso = ConeIso.leftIso Φ ▷ r
  ; rightIso = ConeIso.rightIso Φ ▷ r
  ; compatible =
      isoComp-assoc-at (g ◁ (β ▷ r)) b u ∙
      (isoComp-cong (whisker-mixed-at β r g) (idIso u) ∙
      ((isoComp-assoc-at b′ ((g ◁ β) ▷ r) u) ⁻¹ ∙
      (isoComp-cong (idIso b′) (pre-square-projection f α (g ◁ β)
        (Cone.match s) (Cone.match t) r (ConeIso.compatible Φ)) ∙
        isoComp-assoc-at b′ v (f ◁ (α ▷ r))))) }
  where
  α = ConeIso.leftIso Φ
  β = ConeIso.rightIso Φ
  b = comp-assoc r (Cone.right s) g
  b′ = comp-assoc r (Cone.right t) g
  u = (Cone.match s ▷ r) ∙ (comp-assoc r (Cone.left s) f) ⁻¹
  v = (Cone.match t ▷ r) ∙ (comp-assoc r (Cone.left t) f) ⁻¹

conePre-id : {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (s : Cone f g T) → ConeIso (conePre (id T) s) s
conePre-id {T = T} {f} {g} s = record
  { leftIso = comp-unitʳ (Cone.left s)
  ; rightIso = comp-unitʳ (Cone.right s)
  ; compatible =
      isoComp-assoc-at (g ◁ comp-unitʳ q) (comp-assoc (id T) q g) tail ∙
      (isoComp-cong (right-unitor-comp q g) (idIso tail) ∙
        (unit-square-projection f p (g ∘ q) (Cone.match s)) ⁻¹) }
  where
  p = Cone.left s
  q = Cone.right s
  tail = (Cone.match s ▷ id T) ∙ (comp-assoc (id T) p f) ⁻¹

conePre-assoc : {C D E Q R T : CAT} {f : MAP C E} {g : MAP D E}
  (r : MAP Q R) (s : MAP R T) (c : Cone f g T) →
  ConeIso (conePre r (conePre s c)) (conePre (s ∘ r) c)
conePre-assoc {f = f} {g} r s c = record
  { leftIso = comp-assoc r s p
  ; rightIso = comp-assoc r s q
  ; compatible = step₉ ∙ (step₈ ∙ (step₇ ∙ (step₆ ∙
      (step₅ ∙ (step₄ ∙ (step₃ ∙ (step₂ ∙ step₁))))))) }
  where
  p = Cone.left c
  q = Cone.right c
  τ = Cone.match c
  t = transport-pre f p τ s
  z = transport-pre f p τ (s ∘ r)
  aa = comp-assoc (s ∘ r) q g
  bb = comp-assoc r s (g ∘ q)
  cc = g ◁ comp-assoc r s q
  dd = comp-assoc r (q ∘ s) g
  ee = comp-assoc s q g ▷ r
  uu = t ▷ r
  ii = (comp-assoc r (p ∘ s) f) ⁻¹
  ff = f ◁ comp-assoc r s p
  step₁ = isoComp-assoc-at aa z ff
  step₂ = isoComp-cong (idIso aa) ((transport-pre-assoc f p (g ∘ q) τ s r) ⁻¹)
  step₃ = (isoComp-assoc-at aa (bb ∙ uu) ii) ⁻¹
  step₄ = isoComp-cong ((isoComp-assoc-at aa bb uu) ⁻¹) (idIso ii)
  step₅ = isoComp-cong (isoComp-cong (pentagon-whiskered r s q g) (idIso uu)) (idIso ii)
  step₆ = isoComp-assoc-at cc (dd ∙ ee) (uu ∙ ii) ∙
    isoComp-assoc-at (cc ∙ (dd ∙ ee)) uu ii
  step₇ = isoComp-cong (idIso cc) (isoComp-assoc-at dd ee (uu ∙ ii))
  step₈ = isoComp-cong (idIso cc) (isoComp-cong (idIso dd)
    ((isoComp-assoc-at ee uu ii) ⁻¹))
  step₉ = isoComp-cong (idIso cc) (isoComp-cong (idIso dd)
    (isoComp-cong ((preWhisker-isoComp-at (comp-assoc s q g) t r) ⁻¹) (idIso ii)))
```

## Recovering compatibility after restriction

```agda
cone-pre-compatible : {C D E S T : CAT} {f : MAP C E} {g : MAP D E}
  (r : MAP S T) (s t : Cone f g T)
  (α : (Cone.left s) =₁ (Cone.left t))
  (β : (Cone.right s) =₁ (Cone.right t))
  → (Cone.match (conePre r t) ∙ (f ◁ (α ▷ r))) =₂
      ((g ◁ (β ▷ r)) ∙ Cone.match (conePre r s))
  → ((Cone.match t ∙ (f ◁ α)) ▷ r) =₂ (((g ◁ β) ∙ Cone.match s) ▷ r)
cone-pre-compatible {f = f} {g} r s t α β p =
  (preWhisker-isoComp-at (g ◁ β) (Cone.match s) r) ⁻¹ ∙
  (reflect-transport-square
    (comp-assoc r (Cone.left s) f) (comp-assoc r (Cone.left t) f)
    (comp-assoc r (Cone.right s) g) (comp-assoc r (Cone.right t) g)
    (Cone.match s ▷ r) (Cone.match t ▷ r)
    ((f ◁ α) ▷ r) ((g ◁ β) ▷ r) (f ◁ (α ▷ r)) (g ◁ (β ▷ r))
    (whisker-mixed-at α r f) (whisker-mixed-at β r g) p ∙
    preWhisker-isoComp-at (Cone.match t) (f ◁ α) r)
```
