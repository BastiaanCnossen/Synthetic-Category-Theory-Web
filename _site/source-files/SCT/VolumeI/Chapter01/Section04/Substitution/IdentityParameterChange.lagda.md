# The identity evaluation comparison under substitution

The representing identity is evaluated using its chosen beta comparison.
We first compare beta along a changed tuple of inputs, then account for
the chosen uncurrying comparison. This retains the actual `apply-identity`
from the composition construction.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Substitution.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Substitution.MappingProofCalculus as MappingProofCalculus
import SCT.VolumeI.Chapter01.Section04.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.CompositionNaturality as CompositionNaturality
import SCT.VolumeI.Chapter01.Section04.Substitution.ApplicationRestriction as ApplicationRestriction
import SCT.VolumeI.Chapter01.Section04.Substitution.EvaluationParameterChange as EvaluationParameterChange
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as ProductFunctorUnits
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as IteratedPairing
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as PairingCoherence

module SCT.VolumeI.Chapter01.Section04.Substitution.IdentityParameterChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open MapComposition 𝒯 M
open MappingProofCalculus 𝒯 M using
  (apply-cong-Iso₂; apply-cong-comp; mapUncurry-at-inner; combine-apply; mapUncurry-at-restriction)
open ProductFunctorUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pair-pre-cong-triangle₂)
open IteratedPairing vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pre-inverse-at)
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-left; cancel-right; move-square)
open Structural vocabulary terminal products productLaws composition whiskering
  using (preWhisker-comp-at)
open PairingCoherence vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-triangle₂)

module IdentityTuple {R Γ C : CAT} (p : MAP Γ One) (x : MAP Γ C)
  (r : MAP R Γ) (p′ : MAP R One) (ζ : (p ∘ r) =₁ p′) where

  point = pair p x
  point′ = pair p′ (x ∘ r)
  tupleChange = pair-cong ζ (idIso (x ∘ r)) ∙ pair-pre p x r
  evaluation = mapUncurry (mapId C)
  β = mapId-β C

  evaluated = pair-β₂ p x ∙ (β ▷ point)
  evaluated′ = pair-β₂ p′ (x ∘ r) ∙ (β ▷ point′)

  evaluationChange = (evaluation ◁ tupleChange) ∙ comp-assoc r point evaluation

  abstract
    evaluated-change : (evaluated′ ∙ evaluationChange) =₂ (evaluated ▷ r)
    evaluated-change =
      let projection = isoComp-unitˡ-at _ ∙
            pair-pre-cong-triangle₂ p x r ζ (idIso (x ∘ r))
          a = comp-assoc r point pr₂
          image = (β ▷ point) ▷ r
          betaChange = interchange-at β tupleChange
          moveBeta = preWhisker-comp-at β point r
          expand = isoComp-assoc-at (pair-β₂ p′ (x ∘ r)) (β ▷ point′) evaluationChange
          moveInside = isoComp-assoc-at (pr₂ ◁ tupleChange) (β ▷ (point ∘ r))
              (comp-assoc r point evaluation) ∙
            (isoComp-cong betaChange (idIso (comp-assoc r point evaluation)) ∙
              (isoComp-assoc-at (β ▷ point′) (evaluation ◁ tupleChange)
                (comp-assoc r point evaluation)) ⁻¹)
          project = isoComp-cong projection (idIso (a ∙ image)) ∙
            (isoComp-assoc-at (pair-β₂ p′ (x ∘ r)) (pr₂ ◁ tupleChange) (a ∙ image)) ⁻¹
          cancel = isoComp-assoc-at (pair-β₂ p x ▷ r) (a ⁻¹) (a ∙ image)
          finish = isoComp-cong (idIso (pair-β₂ p x ▷ r)) (cancel-left a image)
      in (preWhisker-isoComp-at (pair-β₂ p x) (β ▷ point) r) ⁻¹ ∙
        (finish ∙ (cancel ∙ (project ∙
        (isoComp-cong (idIso (pair-β₂ p′ (x ∘ r)))
          (isoComp-cong (idIso (pr₂ ◁ tupleChange)) (moveBeta ⁻¹) ∙ moveInside) ∙ expand))))

  nameChange = (mapId C ◁ ζ) ∙ comp-assoc r p (mapId C)
  applicationChange = applyTerm-cong nameChange (idIso (x ∘ r)) ∙
    applyTerm-pre (mapId C ∘ p) x r
  at = mapUncurry-at (mapId C) p x
  at′ = mapUncurry-at (mapId C) p′ (x ∘ r)

  abstract
    uncurryAt-change : (at′ ∙ evaluationChange) =₂
      (applicationChange ∙ (at ▷ r))
    uncurryAt-change =
      let y = x ∘ r
          a = comp-assoc r p (mapId C)
          z = mapId C ◁ ζ
          t = pair-pre p x r
          u = pair-cong ζ (idIso y)
          A = comp-assoc r point evaluation
          tail = applyTerm-pre (mapId C ∘ p) x r ∙ (at ▷ r)
          expand = isoComp-cong (idIso at′)
            (isoComp-assoc-at (evaluation ◁ u) (evaluation ◁ t) A ∙
              isoComp-cong (postWhisker-isoComp-at evaluation u t) (idIso A))
          inner = isoComp-cong (mapUncurry-at-inner (mapId C) ζ (idIso y))
            (idIso ((evaluation ◁ t) ∙ A)) ∙
            (isoComp-assoc-at at′ (evaluation ◁ u) ((evaluation ◁ t) ∙ A)) ⁻¹
          move = isoComp-cong (idIso (applyTerm-cong z (idIso y)))
              ((mapUncurry-at-restriction (mapId C) p x r) ⁻¹) ∙
            isoComp-assoc-at (applyTerm-cong z (idIso y))
              (mapUncurry-at (mapId C) (p ∘ r) y) ((evaluation ◁ t) ∙ A)
          combine = combine-apply z (idIso y) a (idIso y) tail
          normalize = isoComp-cong
            (apply-cong-Iso₂ (idIso nameChange) (isoComp-unitˡ-at (idIso y))) (idIso tail)
      in (isoComp-assoc-at (applyTerm-cong nameChange (idIso y))
          (applyTerm-pre (mapId C ∘ p) x r) (at ▷ r)) ⁻¹ ∙
        (normalize ∙ (combine ∙ (move ∙ (inner ∙ expand))))

  identityEvaluation = evaluated ∙ at ⁻¹
  identityEvaluation′ = evaluated′ ∙ at′ ⁻¹

  abstract
    identityEvaluation-change :
      (identityEvaluation′ ∙ applicationChange) =₂ (identityEvaluation ▷ r)
    identityEvaluation-change =
      let moved = move-square at′ evaluationChange applicationChange (at ▷ r) uncurryAt-change
          inverseImage = (pre-inverse-at at r) ⁻¹
      in (preWhisker-isoComp-at evaluated (at ⁻¹) r) ⁻¹ ∙
        (isoComp-cong (idIso (evaluated ▷ r)) inverseImage ∙
        (isoComp-cong evaluated-change (idIso ((at ▷ r) ⁻¹)) ∙
        ((isoComp-assoc-at evaluated′ evaluationChange ((at ▷ r) ⁻¹)) ⁻¹ ∙
        (isoComp-cong (idIso evaluated′) moved ∙
          isoComp-assoc-at evaluated′ (at′ ⁻¹) applicationChange))))

abstract
  apply-identity-restriction : {R Γ C : CAT}
    (x : MAP Γ C) (σ : MAP R Γ)
    →
        (apply-identity (x ∘ σ) ∙
          (applyTerm-cong (const-pre (mapId C) σ) (idIso (x ∘ σ)) ∙
            applyTerm-pre (identityTerm C) x σ)) =₂
        (apply-identity x ▷ σ)
  apply-identity-restriction {R} {Γ} {C} x σ =
    let module I = IdentityTuple (terminate Γ) x σ (terminate R)
          (terminal-iso (terminate Γ ∘ σ) (terminate R))
        before = isoComp-assoc-at (pair-β₂ (terminate Γ) x)
          (mapId-β C ▷ pair (terminate Γ) x)
          ((mapUncurry-at (mapId C) (terminate Γ) x) ⁻¹)
        after = isoComp-assoc-at (pair-β₂ (terminate R) (x ∘ σ))
          (mapId-β C ▷ pair (terminate R) (x ∘ σ))
          ((mapUncurry-at (mapId C) (terminate R) (x ∘ σ)) ⁻¹)
    in (preWhisker σ ◁ before) ∙
      (I.identityEvaluation-change ∙ isoComp-cong (after ⁻¹) (idIso I.applicationChange))
```

Constant terms have coherent restriction comparisons because all their
unprojected comparison cells have terminal codomain.

```agda
terminal-Iso₂ : {X : CAT} {f g : MAP X One} (α β : f =₁ g) → α =₂ β
terminal-Iso₂ {f = f} {g} α β = equiv-reflect (terminalIso-isEquiv f g) α β (terminal-iso _ _)

abstract
  const-pre-change : {Q R X A : CAT} (x : Obj-abs A)
    (h : MAP R X) (t : MAP Q R) (s : MAP Q X) (δ : (h ∘ t) =₁ s)
    →
        (const-pre x s ∙ ((const x ◁ δ) ∙ comp-assoc t h (const x))) =₂
        (const-pre x t ∙ (const-pre x h ▷ t))
  const-pre-change {Q} {R} {X} x h t s δ =
    let u = terminal-iso (terminate X ∘ h) (terminate R)
        v = terminal-iso (terminate R ∘ t) (terminate Q)
        w = terminal-iso (terminate X ∘ s) (terminate Q)
        z = idIso (terminate Q)
        tail = const-pre x t ∙ (const-pre x h ▷ t)
    in isoComp-unitˡ-at tail ∙
      (isoComp-cong (postWhisker-idIso x (terminate Q)) (idIso tail) ∙
        EvaluationParameterChange.post-change-comparison 𝒯 M x (terminate X) h t s δ
          u v w z (terminal-Iso₂ _ _))

abstract
  apply-identity-natural : {Γ C : CAT} {x y : MAP Γ C} (τ : x =₁ y)
    → (apply-identity y ∙ applyTerm-cong (idIso (identityTerm C)) τ) =₂
        (τ ∙ apply-identity x)
  apply-identity-natural {Γ} {C} {x} {y} τ =
    let p = terminate Γ
        point = pair p x
        point′ = pair p y
        β = mapId-β C
        at = mapUncurry-at (mapId C) p x
        at′ = mapUncurry-at (mapId C) p y
        e = pair-β₂ p x ∙ (β ▷ point)
        e′ = pair-β₂ p y ∙ (β ▷ point′)
        tupleChange = pair-cong (idIso p) τ
        evaluationChange = mapUncurry (mapId C) ◁ tupleChange
        applicationChange = applyTerm-cong (mapId C ◁ idIso p) τ
        evaluationSquare = paste-squares (β ▷ point) (β ▷ point′)
          (pair-β₂ p x) (pair-β₂ p y) evaluationChange (pr₂ ◁ tupleChange) τ
          (interchange-at β tupleChange) (pair-cong-triangle₂ (idIso p) τ)
        inverseSquare = move-square at′ evaluationChange applicationChange at
          (mapUncurry-at-inner (mapId C) (idIso p) τ)
        combined = paste-squares (at ⁻¹) (at′ ⁻¹) e e′
          applicationChange evaluationChange τ inverseSquare evaluationSquare
        oldNormalization = isoComp-assoc-at (pair-β₂ p x) (β ▷ point) (at ⁻¹)
        newNormalization = isoComp-assoc-at (pair-β₂ p y) (β ▷ point′) (at′ ⁻¹)
        normalizeInput = (apply-cong-Iso₂ (postWhisker-idIso (mapId C) p) (idIso τ)) ⁻¹
    in isoComp-cong (idIso τ) oldNormalization ∙
      (combined ∙ isoComp-cong (newNormalization ⁻¹) normalizeInput)

abstract
  apply-identity-change : {R Γ C : CAT} (x : MAP Γ C) (σ : MAP R Γ)
    {y : MAP R C} (τ : (x ∘ σ) =₁ y)
    →
        (apply-identity y ∙
          (applyTerm-cong (const-pre (mapId C) σ) τ ∙ applyTerm-pre (identityTerm C) x σ)) =₂
        (τ ∙ (apply-identity x ▷ σ))
  apply-identity-change {C = C} x σ {y} τ =
    let c = const-pre (mapId C) σ
        q = applyTerm-cong c (idIso (x ∘ σ))
        r = applyTerm-cong (idIso (identityTerm C)) τ
        pre = applyTerm-pre (identityTerm C) x σ
        factor = apply-cong-comp (idIso (identityTerm C)) c τ (idIso (x ∘ σ)) ∙
          (apply-cong-Iso₂ (isoComp-unitˡ-at c) (isoComp-unitʳ-at τ)) ⁻¹
        rearrange = (isoComp-assoc-at (apply-identity y) r (q ∙ pre)) ⁻¹ ∙
          isoComp-cong (idIso (apply-identity y)) (isoComp-assoc-at r q pre)
    in isoComp-cong (idIso τ) (apply-identity-restriction x σ) ∙
      (isoComp-assoc-at τ (apply-identity (x ∘ σ)) (q ∙ pre) ∙
      (isoComp-cong (apply-identity-natural τ) (idIso (q ∙ pre)) ∙
      (rearrange ∙ isoComp-cong (idIso (apply-identity y))
        (isoComp-cong factor (idIso pre)))))
```
