# Transport of the chosen composition

Restriction of the parameter and change of the three endpoints preserve
composition, including the original frames. Both statements follow by
transporting a complete presentation of the chosen composite and comparing
it with the new chosen composite.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.MorphismCompositionTransport where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (MorphismFamily; MorphismFamilyIdentification)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyOperations using (restrict-family; retarget-family)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyComparisons using (inverse-family-comparison)
open import SCT.VolumeI.Chapter02.Section01.Triangles using (short-edges)
open import SCT.VolumeI.Chapter02.Section02.FramedTrianglePresentations
  using (presented-composition; module RestrictPresentation; module RetargetPresentation)
open import SCT.VolumeI.Chapter02.Section02.MorphismCompositionComparisons using (module CompositionComparisons)
import SCT.VolumeI.Chapter02.Section02.MorphismComposition as MC

module CompositionTransport {Γ : Context} (C : CAT Γ) (segal : IsEquiv (short-edges C)) where
  private
    module Chosen = MC.Composition C segal
    module Presentations = CompositionComparisons C segal

  restrict-composition : {P Q : CAT Γ} {f g h : MAP P C}
    (beta : MorphismFamily g h) (alpha : MorphismFamily f g) (r : MAP Q P)
    → MorphismFamilyIdentification One (restrict-family (Chosen.compose beta alpha) r)
        (Chosen.compose (restrict-family beta r) (restrict-family alpha r))
  restrict-composition beta alpha r = inverse-family-comparison
    (presented-composition segal (restrict-family alpha r) (restrict-family beta r)
      (restrict-family (Chosen.compose beta alpha) r)
      (RestrictPresentation.value (Presentations.composition-presentation beta alpha) r))

  retarget-composition : {P : CAT Γ} {f g h f′ g′ h′ : MAP P C}
    (beta : MorphismFamily g h) (alpha : MorphismFamily f g)
    (p : f =₁ f′) (q : g =₁ g′) (r : h =₁ h′)
    → MorphismFamilyIdentification One (retarget-family (Chosen.compose beta alpha) p r)
        (Chosen.compose (retarget-family beta q r) (retarget-family alpha p q))
  retarget-composition beta alpha p q r = inverse-family-comparison
    (presented-composition segal (retarget-family alpha p q) (retarget-family beta q r)
      (retarget-family (Chosen.compose beta alpha) p r)
      (RetargetPresentation.value (Presentations.composition-presentation beta alpha) p q r))
```
