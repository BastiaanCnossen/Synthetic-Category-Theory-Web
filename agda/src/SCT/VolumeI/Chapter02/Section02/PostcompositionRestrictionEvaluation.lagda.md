# Postcomposition commutes with restriction at each endpoint

The edge comparison is lifted through uncurrying with its specified
image. Its endpoint equation retains the actual restriction and
postcomposition evaluation comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.PostcompositionRestrictionEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.EndpointEvaluation 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section07.IsomorphismLifting 𝒯 M ℱ
  using (funIsoReflect; funIsoReflect-β)
open import SCT.VolumeI.Chapter02.Section02.DirectUnitTriangles 𝒯 M ℱ P I E
  using (module ReflectedEndpoint)
import SCT.VolumeI.Chapter02.Section02.RestrictionParameterEvaluation as Restrict
import SCT.VolumeI.Chapter02.Section02.PostcompositionParameterEvaluation as Post
open import SCT.VolumeI.Chapter02.Section02.RestrictionInsertions 𝒯 M ℱ using (insertion)
open import SCT.VolumeI.Chapter01.Section04.ProjectionSquares 𝒯 using (lift-base)
open import SCT.VolumeI.Chapter01.Section08.ProjectionBaseCalculus 𝒯 using (lift-assoc; lift-base-outer)
open import SCT.VolumeI.Chapter01.Section06.InverseCalculus 𝒯 using (pre-inverse)
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.Structural as Structural
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left-reflect)
open Structural vocabulary terminal products productLaws composition whiskering using (whisker-mixed-at)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

module At {Γ A B C D : CAT} (F : MAP C D) (r : MAP A B) (h : MAP Γ (Fun B C)) where
  H = funUncurry h
  hF = funPost F ∘ h
  hR = funPre r ∘ h
  source = funPre r ∘ hF
  target = funPost F ∘ hR
  HF = funUncurry hF
  HR = funUncurry hR
  L = productMap (id Γ) r
  q = funPre-uncurry r h
  qF = funPre-uncurry r hF
  φ = funPost-uncurry F h
  ψ = funPost-uncurry F hR
  aH = comp-assoc L H F
  leading = aH ∙ ((φ ▷ L) ∙ qF)
  θ = (F ◁ q) ⁻¹ ∙ leading
  raw = ψ ⁻¹ ∙ θ
  edge-comparison : source =₁ target
  edge-comparison = funIsoReflect source target raw

  module Endpoint (z : Obj-abs A) where
    i = insert {X = Γ} z
    j = insert {X = Γ} (r ∘ z)
    χ = insertion Γ r z
    prefix = lift-base H L i χ
    prefixF = lift-base (F ∘ H) L i χ
    prefixHF = lift-base HF L i χ
    Q = evaluate-uncurry z hR
    Qsource = evaluate-uncurry z source
    Qtarget = evaluate-uncurry z target
    Qvertex = evaluate-uncurry (r ∘ z) h
    QvertexF = evaluate-uncurry (r ∘ z) hF
    pre = (evaluate-pre r z ▷ h) ∙ (comp-assoc h (funPre r) (evaluate z)) ⁻¹
    preF = (evaluate-pre r z ▷ hF) ∙ (comp-assoc hF (funPre r) (evaluate z)) ⁻¹
    post = evaluate-post-at z F hR
    postVertex = evaluate-post-at (r ∘ z) F h
    δ = evaluate z ◁ edge-comparison
    aQ = comp-assoc i HR F
    aL = comp-assoc i (H ∘ L) F
    aVertex = comp-assoc j H F
    fq = F ◁ q
    module Reflected = ReflectedEndpoint z source target ψ θ edge-comparison
      (funIsoReflect-β source target raw)

    abstract
      restriction-image : (Qvertex ∙ pre) =₂ (prefix ∙ ((q ▷ i) ∙ Q))
      restriction-image = (isoComp-assoc-at (H ◁ χ) (comp-assoc i L H) ((q ▷ i) ∙ Q)) ⁻¹ ∙
        Restrict.At.comparison 𝒯 M ℱ r h z

      cancel-edge : ((fq ▷ i) ∙ (θ ▷ i)) =₂ (leading ▷ i)
      cancel-edge = (preWhisker i ◁ cancel-inverse fq leading) ∙
        (preWhisker-isoComp-at fq θ i) ⁻¹

      left-normal :
        ((F ◁ Qvertex) ∙ ((F ◁ pre) ∙ (post ∙ δ))) =₂
        ((F ◁ prefix) ∙ (aL ∙ ((leading ▷ i) ∙ Qsource)))
      left-normal =
        isoComp-cong (idIso (F ◁ prefix))
          (isoComp-cong (idIso aL)
            (isoComp-cong cancel-edge (idIso Qsource) ∙
              (isoComp-assoc-at (fq ▷ i) (θ ▷ i) Qsource) ⁻¹) ∙
            isoComp-assoc-at aL (fq ▷ i) ((θ ▷ i) ∙ Qsource)) ∙
        isoComp-cong (idIso (F ◁ prefix))
          (isoComp-cong ((whisker-mixed-at q i F) ⁻¹) (idIso ((θ ▷ i) ∙ Qsource)) ∙
            (isoComp-assoc-at (F ◁ (q ▷ i)) aQ ((θ ▷ i) ∙ Qsource)) ⁻¹) ∙
        isoComp-cong (idIso (F ◁ prefix))
          (isoComp-cong (idIso (F ◁ (q ▷ i)))
            (isoComp-cong (idIso aQ) Reflected.endpoint ∙
              isoComp-assoc-at aQ ((ψ ▷ i) ∙ Qtarget) δ)) ∙
        isoComp-cong (idIso (F ◁ prefix))
          (isoComp-cong (idIso (F ◁ (q ▷ i)))
            (isoComp-cong ((Post.At.comparison 𝒯 M ℱ F hR z) ⁻¹) (idIso δ) ∙
              (isoComp-assoc-at (F ◁ Q) post δ) ⁻¹)) ∙
        isoComp-cong (idIso (F ◁ prefix)) (isoComp-assoc-at (F ◁ (q ▷ i)) (F ◁ Q) (post ∙ δ)) ∙
        isoComp-assoc-at (F ◁ prefix) ((F ◁ (q ▷ i)) ∙ (F ◁ Q)) (post ∙ δ) ∙
        isoComp-cong
          (isoComp-cong (idIso (F ◁ prefix)) (postWhisker-isoComp-at F (q ▷ i) Q) ∙
            postWhisker-isoComp-at F prefix ((q ▷ i) ∙ Q) ∙
            (postWhisker F ◁ restriction-image) ∙
            (postWhisker-isoComp-at F Qvertex pre) ⁻¹) (idIso (post ∙ δ)) ∙
        (isoComp-assoc-at (F ◁ Qvertex) (F ◁ pre) (post ∙ δ)) ⁻¹

      leading-image : (leading ▷ i) =₂
        ((aH ▷ i) ∙ (((φ ▷ L) ▷ i) ∙ (qF ▷ i)))
      leading-image = isoComp-cong (idIso (aH ▷ i)) (preWhisker-isoComp-at (φ ▷ L) qF i) ∙
        preWhisker-isoComp-at aH ((φ ▷ L) ∙ qF) i

      middle-normal : ((F ◁ prefix) ∙ (aL ∙ ((leading ▷ i) ∙ Qsource))) =₂
        (aVertex ∙ ((φ ▷ j) ∙ (prefixHF ∙ ((qF ▷ i) ∙ Qsource))))
      middle-normal =
        isoComp-cong (idIso aVertex) (isoComp-assoc-at (φ ▷ j) prefixHF ((qF ▷ i) ∙ Qsource)) ∙
        isoComp-cong (idIso aVertex)
          (isoComp-cong (lift-base-outer L j i χ φ) (idIso ((qF ▷ i) ∙ Qsource))) ∙
        isoComp-cong (idIso aVertex)
          ((isoComp-assoc-at prefixF ((φ ▷ L) ▷ i) ((qF ▷ i) ∙ Qsource)) ⁻¹) ∙
        isoComp-assoc-at aVertex prefixF (((φ ▷ L) ▷ i) ∙ ((qF ▷ i) ∙ Qsource)) ∙
        isoComp-cong ((lift-assoc L j i χ H F) ⁻¹)
          (idIso (((φ ▷ L) ▷ i) ∙ ((qF ▷ i) ∙ Qsource))) ∙
        (isoComp-assoc-at ((F ◁ prefix) ∙ aL) (aH ▷ i)
          (((φ ▷ L) ▷ i) ∙ ((qF ▷ i) ∙ Qsource))) ⁻¹ ∙
        (isoComp-assoc-at (F ◁ prefix) aL
          ((aH ▷ i) ∙ (((φ ▷ L) ▷ i) ∙ ((qF ▷ i) ∙ Qsource)))) ⁻¹ ∙
        isoComp-cong (idIso (F ◁ prefix)) (isoComp-cong (idIso aL)
          (isoComp-cong (idIso (aH ▷ i)) (isoComp-assoc-at ((φ ▷ L) ▷ i) (qF ▷ i) Qsource) ∙
            isoComp-assoc-at (aH ▷ i) (((φ ▷ L) ▷ i) ∙ (qF ▷ i)) Qsource ∙
            isoComp-cong leading-image (idIso Qsource)))

      restriction-imageF : (QvertexF ∙ preF) =₂ (prefixHF ∙ ((qF ▷ i) ∙ Qsource))
      restriction-imageF = (isoComp-assoc-at (HF ◁ χ) (comp-assoc i L HF) ((qF ▷ i) ∙ Qsource)) ⁻¹ ∙
        Restrict.At.comparison 𝒯 M ℱ r hF z

      right-normal : (aVertex ∙ ((φ ▷ j) ∙ (prefixHF ∙ ((qF ▷ i) ∙ Qsource)))) =₂
        ((F ◁ Qvertex) ∙ (postVertex ∙ preF))
      right-normal = isoComp-assoc-at (F ◁ Qvertex) postVertex preF ∙
        isoComp-cong (Post.At.comparison 𝒯 M ℱ F h (r ∘ z)) (idIso preF) ∙
        (isoComp-assoc-at aVertex ((φ ▷ j) ∙ QvertexF) preF) ⁻¹ ∙
        isoComp-cong (idIso aVertex) ((isoComp-assoc-at (φ ▷ j) QvertexF preF) ⁻¹) ∙
        isoComp-cong (idIso aVertex) (isoComp-cong (idIso (φ ▷ j)) (restriction-imageF ⁻¹))

      comparison : ((F ◁ pre) ∙ (post ∙ δ)) =₂ (postVertex ∙ preF)
      comparison = cancel-left-reflect (F ◁ Qvertex) (right-normal ∙ middle-normal ∙ left-normal)
```
