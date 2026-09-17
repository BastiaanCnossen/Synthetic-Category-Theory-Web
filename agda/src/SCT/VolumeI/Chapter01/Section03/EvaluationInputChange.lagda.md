# Simultaneous evaluation and change of parameter

The product comparison used to restrict an evaluation also accepts an
arbitrary pair of inputs. We compare this instance with successive
restriction and evaluation, retaining the chosen product comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.Currying as Currying
import SCT.VolumeI.Chapter01.Section03.Compatibility as Compatibility
import SCT.VolumeI.Chapter01.Section03.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section03.CompositionNaturality as CompositionNaturality
import SCT.VolumeI.Chapter01.Section03.EvaluationParameterChange as EvaluationParameterChange
import SCT.VolumeI.Chapter01.Section03.ProductAssociativity as ProductAssociativity
import SCT.VolumeI.Chapter01.Section03.ProductSubstitution as ProductSubstitution
import SCT.VolumeI.Chapter01.Section03.ProductSecondCoordinate as ProductSecondCoordinate
import SCT.VolumeI.Chapter01.Section02.ProductFunctorUnits as ProductFunctorUnits
import SCT.VolumeI.Chapter01.Section02.IteratedPairing as IteratedPairing
import SCT.VolumeI.Chapter01.Section02.Structural as Structural
import SCT.VolumeI.Chapter01.Section01.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section03.EvaluationInputChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open Currying 𝒯 M using (mapUncurry-pre)
open Compatibility 𝒯 M using (slice-comparison)
open MapComposition 𝒯 M
open CompositionNaturality 𝒯 M using (coordinate-at)
open EvaluationParameterChange 𝒯 M using (module AtCoordinates; coordinate-at-change; post-change-comparison)
open ProductAssociativity 𝒯 M using (module PairingAssembly; cancel-forward)
module ProductCoordinates = ProductSubstitution.Coordinates 𝒯 M
open ProductSecondCoordinate 𝒯 M using (second-normalization)
open ProductFunctorUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pair-pre-cong-triangle₁; pair-pre-cong-triangle₂; left-unitor-comp)
open IteratedPairing vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pentagon-whiskered)
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-comp-at; postWhisker-id-at; preWhisker-comp-at)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering
  using (reassociateFour; cancel-inverse)

coordinate-at-outer-composition : {R K X Y Z : CAT}
  (F : MAP Y Z) (G : MAP X Y) (π : MAP K X) (t : MAP R K)
  {p : MAP R X} (b : NatIso (π ∘ t) p)
  → Iso₂ (comp-assoc p G F ∙ coordinate-at (F ∘ G) π t b)
      ((F ◁ coordinate-at G π t b) ∙
        (comp-assoc t (G ∘ π) F ∙ (comp-assoc π G F ▷ t)))
coordinate-at-outer-composition F G π t {p} b =
  let A = comp-assoc p G F
      B = (F ∘ G) ◁ b
      C = comp-assoc t π (F ∘ G)
      D = F ◁ (G ◁ b)
      E = comp-assoc (π ∘ t) G F
      I = F ◁ comp-assoc t π G
      J = comp-assoc t (G ∘ π) F
      K = comp-assoc π G F ▷ t
  in isoComp-cong (invIso (postWhisker-isoComp-at F (G ◁ b) (comp-assoc t π G))) (idIso (J ∙ K)) ∙
    (invIso (isoComp-assoc-at D I (J ∙ K)) ∙
    (isoComp-cong (idIso D) (pentagon-whiskered t π G F) ∙
    (isoComp-assoc-at D E C ∙
    (isoComp-cong (postWhisker-comp-at b G F) (idIso C) ∙ invIso (isoComp-assoc-at A B C)))))

at-second-normalization : {Γ X Y C : CAT} (f : MAP X Y) (p : MAP Γ X) (x : MAP Γ C)
  → Iso₂ (AtCoordinates.second f p x) (pair-β₂ p x ∙ (comp-unitˡ pr₂ ▷ pair p x))
at-second-normalization {C = C} f p x =
  isoComp-cong (idIso (pair-β₂ p x)) (left-unitor-comp (pair p x) pr₂) ∙
    (isoComp-assoc-at (pair-β₂ p x) (comp-unitˡ (pr₂ ∘ pair p x)) (comp-assoc (pair p x) pr₂ (id C)) ∙
    (isoComp-cong (postWhisker-id-at (pair-β₂ p x)) (idIso (comp-assoc (pair p x) pr₂ (id C))) ∙
      invIso (isoComp-assoc-at (comp-unitˡ x) (id C ◁ pair-β₂ p x) (comp-assoc (pair p x) pr₂ (id C)))))

at-comparison-projection₁ : {Γ X Y C : CAT} (f : MAP X Y) (p : MAP Γ X) (x : MAP Γ C)
  → Iso₂ (pair-β₁ (f ∘ p) x ∙ (pr₁ ◁ AtCoordinates.comparison f p x))
      (AtCoordinates.first f p x ∙
        ((pair-β₁ (f ∘ pr₁) (id C ∘ pr₂) ▷ pair p x) ∙
          invIso (comp-assoc (pair p x) (productMap f (id C)) pr₁)))
at-comparison-projection₁ {C = C} f p x =
  pair-pre-cong-triangle₁ (f ∘ pr₁) (id C ∘ pr₂) (pair p x)
    (AtCoordinates.first f p x) (AtCoordinates.second f p x) ∙
      isoComp-cong (idIso (pair-β₁ (f ∘ p) x)) (postWhisker pr₁ ◁ AtCoordinates.normalization f p x)

at-comparison-projection₂ : {Γ X Y C : CAT} (f : MAP X Y) (p : MAP Γ X) (x : MAP Γ C)
  → Iso₂ (pair-β₂ (f ∘ p) x ∙ (pr₂ ◁ AtCoordinates.comparison f p x))
      (AtCoordinates.second f p x ∙
        ((pair-β₂ (f ∘ pr₁) (id C ∘ pr₂) ▷ pair p x) ∙
          invIso (comp-assoc (pair p x) (productMap f (id C)) pr₂)))
at-comparison-projection₂ {C = C} f p x =
  pair-pre-cong-triangle₂ (f ∘ pr₁) (id C ∘ pr₂) (pair p x)
    (AtCoordinates.first f p x) (AtCoordinates.second f p x) ∙
      isoComp-cong (idIso (pair-β₂ (f ∘ p) x)) (postWhisker pr₂ ◁ AtCoordinates.normalization f p x)

first-input-change : {Γ Q P Y C : CAT}
  (f : MAP P Y) (σ : MAP Q P) (p : MAP Γ Q) (x : MAP Γ C)
  → Iso₂
      (AtCoordinates.first f (σ ∘ p) x ∙
        (((f ∘ pr₁) ◁ AtCoordinates.comparison σ p x) ∙
          comp-assoc (pair p x) (productMap σ (id C)) (f ∘ pr₁)))
      (comp-assoc p σ f ∙
        (AtCoordinates.first (f ∘ σ) p x ∙ (ProductCoordinates.first C f σ ▷ pair p x)))
first-input-change {C = C} f σ p x =
  let h = productMap σ (id C)
      t = pair p x
      n = AtCoordinates.comparison σ p x
      b = pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂)
      c = AtCoordinates.first σ p x
      original = coordinate-at f pr₁ h b
      u = ProductCoordinates.first C f σ
      w = AtCoordinates.first (f ∘ σ) p x
      A = comp-assoc p σ f
      corner = comp-assoc pr₁ σ f
      mid = comp-assoc t (σ ∘ pr₁) f
      simplify = (preWhisker t ◁ cancel-forward corner original) ∙
        invIso (preWhisker-isoComp-at corner u t)
      normalizeLong = isoComp-cong (idIso (f ◁ c)) (isoComp-cong (idIso mid) simplify) ∙
        (isoComp-cong (idIso (f ◁ c)) (isoComp-assoc-at mid (corner ▷ t) (u ▷ t)) ∙
        (isoComp-assoc-at (f ◁ c) (mid ∙ (corner ▷ t)) (u ▷ t) ∙
        (isoComp-cong (coordinate-at-outer-composition f σ pr₁ t (pair-β₁ p x)) (idIso (u ▷ t)) ∙
          invIso (isoComp-assoc-at A w (u ▷ t)))))
  in invIso normalizeLong ∙
    coordinate-at-change f pr₁ h t (pair (σ ∘ p) x) n b (pair-β₁ (σ ∘ p) x) c
      (at-comparison-projection₁ σ p x)

second-input-change : {Γ Q P Y C : CAT}
  (f : MAP P Y) (σ : MAP Q P) (p : MAP Γ Q) (x : MAP Γ C)
  → Iso₂
      (AtCoordinates.second f (σ ∘ p) x ∙
        (((id C ∘ pr₂) ◁ AtCoordinates.comparison σ p x) ∙
          comp-assoc (pair p x) (productMap σ (id C)) (id C ∘ pr₂)))
      (idIso x ∙
        (AtCoordinates.second (f ∘ σ) p x ∙ (ProductCoordinates.second C f σ ▷ pair p x)))
second-input-change {C = C} f σ p x =
  let h = productMap σ (id C)
      t = pair p x
      n = AtCoordinates.comparison σ p x
      q = id C ∘ pr₂
      v = comp-unitˡ pr₂
      b = pair-β₂ (σ ∘ pr₁) (id C ∘ pr₂)
      b′ = pair-β₂ (σ ∘ p) x
      S = ProductCoordinates.second C f σ
      T = AtCoordinates.second (f ∘ σ) p x
      Aq = comp-assoc t h q
      Aπ = comp-assoc t h pr₂
      vv = (v ▷ h) ▷ t
      normalized = T ∙ (S ▷ t)
      leftStart = invIso (isoComp-assoc-at b′ (pr₂ ◁ n) ((v ▷ (h ∘ t)) ∙ Aq)) ∙
        (isoComp-cong (idIso b′) (isoComp-assoc-at (pr₂ ◁ n) (v ▷ (h ∘ t)) Aq) ∙
        (isoComp-cong (idIso b′) (isoComp-cong (interchange-at v n) (idIso Aq)) ∙
        (reassociateFour b′ (v ▷ pair (σ ∘ p) x) (q ◁ n) Aq ∙
          isoComp-cong (at-second-normalization f (σ ∘ p) x) (idIso ((q ◁ n) ∙ Aq)))))
      middle = isoComp-cong (at-comparison-projection₂ σ p x) (invIso (preWhisker-comp-at v h t))
      cancellation = isoComp-cong (idIso T)
          (isoComp-cong (idIso (b ▷ t))
            (isoComp-unitˡ-at vv ∙
              (isoComp-cong (isoComp-inverseˡ-at Aπ) (idIso vv) ∙
                invIso (isoComp-assoc-at (invIso Aπ) Aπ vv))) ∙
            isoComp-assoc-at (b ▷ t) (invIso Aπ) (Aπ ∙ vv)) ∙
        isoComp-assoc-at T ((b ▷ t) ∙ invIso Aπ) (Aπ ∙ vv)
      rightFinish = isoComp-cong (idIso T)
        ((preWhisker t ◁ invIso (second-normalization C f σ)) ∙
          invIso (preWhisker-isoComp-at b (v ▷ h) t))
  in invIso (isoComp-unitˡ-at normalized) ∙ (rightFinish ∙ (cancellation ∙ (middle ∙ leftStart)))

at-input-change : {Γ Q P Y C : CAT}
  (f : MAP P Y) (σ : MAP Q P) (p : MAP Γ Q) (x : MAP Γ C)
  → Iso₂
      (AtCoordinates.comparison f (σ ∘ p) x ∙
        ((productMap f (id C) ◁ AtCoordinates.comparison σ p x) ∙
          comp-assoc (pair p x) (productMap σ (id C)) (productMap f (id C))))
      (pair-cong (comp-assoc p σ f) (idIso x) ∙
        (AtCoordinates.comparison (f ∘ σ) p x ∙ (slice-comparison {C = C} f σ ▷ pair p x)))
at-input-change {C = C} f σ p x =
  let u = ProductCoordinates.first C f σ
      v = ProductCoordinates.second C f σ
      w = AtCoordinates.first (f ∘ σ) p x
      z = AtCoordinates.second (f ∘ σ) p x
      a = AtCoordinates.first f (σ ∘ p) x
      d = AtCoordinates.second f (σ ∘ p) x
      η = comp-assoc p σ f
      θ = idIso x
      assembled = PairingAssembly.assemble (f ∘ pr₁) (id C ∘ pr₂)
        (productMap σ (id C)) (pair p x) (pair (σ ∘ p) x) (AtCoordinates.comparison σ p x)
        u v w z a d η θ (first-input-change f σ p x) (second-input-change f σ p x)
      normalizeShort = isoComp-cong (AtCoordinates.normalization f (σ ∘ p) x) (idIso _)
      normalizeLong = isoComp-cong (idIso (pair-cong η θ))
        (isoComp-cong (AtCoordinates.normalization (f ∘ σ) p x)
          (preWhisker (pair p x) ◁ ProductCoordinates.normalization C f σ))
  in invIso normalizeLong ∙ (assembled ∙ normalizeShort)

forward-uncurry-pre : {P Q C D : CAT} (f : MAP P (Map C D)) (σ : MAP Q P)
  → NatIso (mapUncurry f ∘ productMap σ (id C)) (mapUncurry (f ∘ σ))
forward-uncurry-pre {C = C} f σ = (mapEval ◁ slice-comparison f σ) ∙
  comp-assoc (productMap σ (id C)) (productMap f (id C)) mapEval

forward-uncurry-pre-cancel : {P Q C D : CAT} (f : MAP P (Map C D)) (σ : MAP Q P)
  → Iso₂ (forward-uncurry-pre f σ ∙ mapUncurry-pre f σ) (idIso (mapUncurry (f ∘ σ)))
forward-uncurry-pre-cancel {C = C} f σ =
  let κ = slice-comparison {C = C} f σ
      A = comp-assoc (productMap σ (id C)) (productMap f (id C)) mapEval
  in postWhisker-idIso mapEval (productMap (f ∘ σ) (id C)) ∙
    ((postWhisker mapEval ◁ isoComp-inverseʳ-at κ) ∙
    (invIso (postWhisker-isoComp-at mapEval κ (invIso κ)) ∙
    (isoComp-cong (idIso (mapEval ◁ κ)) (cancel-inverse A (mapEval ◁ invIso κ)) ∙
      isoComp-assoc-at (mapEval ◁ κ) A (invIso A ∙ (mapEval ◁ invIso κ)))))

mapUncurry-at-input-change : {Γ Q P C D : CAT}
  (f : MAP P (Map C D)) (σ : MAP Q P) (p : MAP Γ Q) (x : MAP Γ C)
  → let n = AtCoordinates.comparison σ p x
    in Iso₂
      (applyTerm-cong (comp-assoc p σ f) (idIso x) ∙ mapUncurry-at (f ∘ σ) p x)
      (mapUncurry-at f (σ ∘ p) x ∙
        ((mapUncurry f ◁ n) ∙
          (comp-assoc (pair p x) (productMap σ (id C)) (mapUncurry f) ∙
            (mapUncurry-pre f σ ▷ pair p x))))
mapUncurry-at-input-change {C = C} f σ p x =
  let t = pair p x
      n = AtCoordinates.comparison σ p x
      A = comp-assoc t (productMap σ (id C)) (mapUncurry f)
      before = forward-uncurry-pre f σ ▷ t
      back = mapUncurry-pre f σ ▷ t
      target = applyTerm-cong (comp-assoc p σ f) (idIso x) ∙ mapUncurry-at (f ∘ σ) p x
      short = mapUncurry-at f (σ ∘ p) x
      step = mapUncurry f ◁ n
      cancel = preWhisker-idIso (mapUncurry (f ∘ σ)) t ∙
        ((preWhisker t ◁ forward-uncurry-pre-cancel f σ) ∙
          invIso (preWhisker-isoComp-at (forward-uncurry-pre f σ) (mapUncurry-pre f σ) t))
      compare = invIso (isoComp-assoc-at (applyTerm-cong (comp-assoc p σ f) (idIso x))
          (mapUncurry-at (f ∘ σ) p x) before) ∙
        post-change-comparison mapEval (productMap f (id C)) (productMap σ (id C)) t
          (pair (σ ∘ p) x) n (slice-comparison f σ) (AtCoordinates.comparison (f ∘ σ) p x)
          (AtCoordinates.comparison f (σ ∘ p) x)
          (pair-cong (comp-assoc p σ f) (idIso x)) (at-input-change f σ p x)
  in isoComp-cong (idIso short) (isoComp-assoc-at step A back) ∙
    (isoComp-assoc-at short (step ∙ A) back ∙
    (isoComp-cong (invIso compare) (idIso back) ∙
    (invIso (isoComp-assoc-at target before back) ∙
    (isoComp-cong (idIso target) (invIso cancel) ∙ invIso (isoComp-unitʳ-at target)))))
```
```
