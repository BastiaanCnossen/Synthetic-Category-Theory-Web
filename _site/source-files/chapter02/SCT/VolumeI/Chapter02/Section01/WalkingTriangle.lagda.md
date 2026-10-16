# The walking triangle and its interval families

The walking triangle is the arrow category of the interval. Its vertices
are the two constant arrows and the identity arrow. The middle face is
the literal curried first projection, and the two degeneracies evaluate
at the interval endpoints.

Initiality and terminality provide the remaining two faces. The conditional
families below factor the endpoint map through the chosen inverse of the
corresponding endpoint-fiber projection. Their source and target frames
come from the same complete factorization triangle. The final definitions instantiate these constructions with the interval
initiality and terminality clauses from HomAndSlices. Their endpoint frames
and constant evaluation give the six face-degeneracy equations. The framed
vertex comparisons are constructed below from the same endpoint fibers.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.WalkingTriangle where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyOperations using (restrict-family; retarget-family)
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence using (comp-assoc; module Composition)
open Composition
import SCT.VolumeI.Chapter01.Section03.Factorizations as Fact
open import SCT.VolumeI.Chapter01.Section06.Cones using (Cone)
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter01.Section07.Currying using (funCurry)
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun using (funName)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1]; zero; one)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (Ar; ev₀; ev₁; MorphismFamily; evAt-constant)
open import SCT.VolumeI.Chapter02.Section01.HomAndSlices
  using (interval-zero-initial; interval-one-terminal)


module _ {Γ : Context} where
  [2] : CAT Γ
  [2] = Ar [1]

  vertex₀ vertex₁ vertex₂ : MAP One [2]
  vertex₀ = funName (const zero)
  vertex₁ = funName (id [1])
  vertex₂ = funName (const one)

  d₁ : MAP [1] [2]
  d₁ = funCurry (pr₁ {C = [1]} {D = [1]})

  s₀ s₁ : MAP [2] [1]
  s₀ = ev₀
  s₁ = ev₁

private
  module _ {Γ : Context} {P C : CAT Γ} (f g : MAP P C) where
    endpoint-factor-family : Fact.Factorization (pair (ev₀ {C = C}) ev₁) (pair f g)
      → MorphismFamily f g
    endpoint-factor-family F = record
      { arrow = Fact.factor F
      ; source-frame = pair-β₁ f g ∙
          ((pr₁ ◁ Fact.triangle F) ∙
            (comp-assoc (Fact.factor F) (pair ev₀ ev₁) pr₁ ∙
              ((pair-β₁ ev₀ ev₁) ⁻¹ ▷ Fact.factor F)))
      ; target-frame = pair-β₂ f g ∙
          ((pr₂ ◁ Fact.triangle F) ∙
            (comp-assoc (Fact.factor F) (pair ev₀ ev₁) pr₂ ∙
              ((pair-β₂ ev₀ ev₁) ⁻¹ ▷ Fact.factor F))) }

    endpoint-selected-factor :
      IsEquiv (pullback₂ {f = pair (ev₀ {C = C}) ev₁} {g = pair f g})
      → Fact.Factorization (pair (ev₀ {C = C}) ev₁) (pair f g)
    endpoint-selected-factor e = Fact.factorization-from-equivalent-source
      (pair f g) (pair (ev₀ {C = C}) ev₁) pullback₂ pullback₁ e
      ((Cone.match (pullback-cone (pair (ev₀ {C = C}) ev₁) (pair f g))) ⁻¹)

module _ {Γ : Context} where
  minimum-family :
    IsEquiv (pullback₂ {f = pair (ev₀ {C = [1] {Γ = Γ}}) ev₁} {g = pair (const zero) (id [1])})
    → MorphismFamily (const zero) (id [1])
  minimum-family e = endpoint-factor-family (const zero) (id [1])
    (endpoint-selected-factor (const zero) (id [1]) e)

  maximum-family :
    IsEquiv (pullback₂ {f = pair (ev₀ {C = [1] {Γ = Γ}}) ev₁} {g = pair (id [1]) (const one)})
    → MorphismFamily (id [1]) (const one)
  maximum-family e = endpoint-factor-family (id [1]) (const one)
    (endpoint-selected-factor (id [1]) (const one) e)


module _ {Γ : Context} where
  minimum : MorphismFamily (const (zero {Γ = Γ})) (id [1])
  minimum = minimum-family interval-zero-initial

  maximum : MorphismFamily (id ([1] {Γ = Γ})) (const one)
  maximum = maximum-family interval-one-terminal

  d₂ d₀ : MAP ([1] {Γ = Γ}) [2]
  d₂ = MorphismFamily.arrow minimum
  d₀ = MorphismFamily.arrow maximum

  s₀-d₂ : (s₀ ∘ d₂) =₁ const (zero {Γ = Γ})
  s₀-d₂ = MorphismFamily.source-frame minimum
  s₁-d₂ : (s₁ ∘ d₂) =₁ id ([1] {Γ = Γ})
  s₁-d₂ = MorphismFamily.target-frame minimum

  s₀-d₀ : (s₀ ∘ d₀) =₁ id ([1] {Γ = Γ})
  s₀-d₀ = MorphismFamily.source-frame maximum
  s₁-d₀ : (s₁ ∘ d₀) =₁ const (one {Γ = Γ})
  s₁-d₀ = MorphismFamily.target-frame maximum

  s₀-d₁ : (s₀ ∘ d₁) =₁ id ([1] {Γ = Γ})
  s₀-d₁ = evAt-constant zero
  s₁-d₁ : (s₁ ∘ d₁) =₁ id ([1] {Γ = Γ})
  s₁-d₁ = evAt-constant one
```

The common vertices are compared as arrows with their specified endpoints.
Initiality compares the bottom and middle vertices; terminality compares
the top vertex. The endpoint-fiber argument retains both endpoint
equations of each comparison.

```agda
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; postWhisker-id₌; comp-unitˡ; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction
open import SCT.VolumeI.Chapter01.Section03.Identifications.IdentificationSquares
  using (project-composite)
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
open import SCT.VolumeI.Chapter01.Section03.WhiskeringEquivalence
  using (factor-through-postWhisker)
import SCT.VolumeI.Chapter01.Section03.Factorizations as Fact
open import SCT.VolumeI.Chapter02.Section01.HomAndSlices
  using (module EndpointFiber; endpointMap; IsInitial; IsTerminal)
open import SCT.VolumeI.Chapter02.Section01.Morphisms

private
  module _ {Γ : Context} where
    project-frame : {P K E C : CAT Γ}
      (π : MAP K E) (r : MAP E C) (s : MAP K C)
      (projection : (r ∘ π) =₁ s)
      {u v : MAP P K} (δ : u =₁ v)
      {w : MAP P E} {f : MAP P C}
      (h : (π ∘ u) =₁ w) (h′ : (π ∘ v) =₁ w)
      (k : (r ∘ w) =₁ f)
      (a : (s ∘ u) =₁ f) (b : (s ∘ v) =₁ f)
      → (k ∙ (r ◁ h)) =₂ (a ∙ restrict-triangle r π projection u)
      → (k ∙ (r ◁ h′)) =₂ (b ∙ restrict-triangle r π projection v)
      → CompatibleOver π h h′ δ
      → CompatibleOver s a b δ
    project-frame π r s projection {u} {v} δ h h′ k a b first second given =
      cancel-right p
        (paired ∙
          ((comp₌-assoc b p′ t) ⁻¹ ∙
            (comp₌-cong (id₌ b) (natural ⁻¹) ∙
              comp₌-assoc b (s ◁ δ) p)))
      where
        p = restrict-triangle r π projection u
        p′ = restrict-triangle r π projection v
        t = r ◁ (π ◁ δ)
        natural = restrict-change-square-One r π s projection δ
        projected = comp₌-cong (id₌ k)
          ((postWhisker r ◁ given) ∙
            (postWhisker-comp₌ r h′ (π ◁ δ)) ⁻¹) ∙
          comp₌-assoc k (r ◁ h′) t
        paired = first ∙ (projected ∙ comp₌-cong (second ⁻¹) (id₌ t))

    constant-frame-compatible : {P K C : CAT Γ} (π : MAP K C)
      {u v : MAP P K} {f : MAP P C}
      (a : (π ∘ u) =₁ f) (b : (π ∘ v) =₁ f) (δ : u =₁ v)
      → CompatibleOver π a b δ
      → (const b ∙ (π ◁ δ)) =₁ const a
    constant-frame-compatible π {u} {v} {f} a b δ given =
      comp₌-unitˡ (const a) ∙
        compatible-to-over
          {X = category-over _ f} {Y = category-over _ π}
          {F = functor-over u a} {G = functor-over v b} given

    endpoint-triangle : {P C : CAT Γ} {f g : MAP P C}
      (α : MorphismFamily f g)
      → (pair ev₀ ev₁ ∘ MorphismFamily.arrow α) =₁ pair f g
    endpoint-triangle α =
      pair⁼ (MorphismFamily.source-frame α) (MorphismFamily.target-frame α) ∙
        pair-pre ev₀ ev₁ (MorphismFamily.arrow α)

    decode-endpoint-comparison : {P C : CAT Γ} {f g : MAP P C}
      (α β : MorphismFamily f g)
      (δ : MorphismFamily.arrow α =₁ MorphismFamily.arrow β)
      → CompatibleOver (pair ev₀ ev₁)
          (endpoint-triangle α) (endpoint-triangle β) δ
      → MorphismFamilyIdentification One α β
    decode-endpoint-comparison {f = f} {g} α β δ given = record
      { identification = δ
      ; source-compatible = constant-frame-compatible ev₀
          (MorphismFamily.source-frame α) (MorphismFamily.source-frame β) δ
          (project-frame (pair ev₀ ev₁) pr₁ ev₀ (pair-β₁ ev₀ ev₁) δ
            (endpoint-triangle α) (endpoint-triangle β) (pair-β₁ f g)
            (MorphismFamily.source-frame α) (MorphismFamily.source-frame β)
            (pair-evaluation-over₁-One ev₀ ev₁ (MorphismFamily.arrow α)
              (MorphismFamily.source-frame α) (MorphismFamily.target-frame α))
            (pair-evaluation-over₁-One ev₀ ev₁ (MorphismFamily.arrow β)
              (MorphismFamily.source-frame β) (MorphismFamily.target-frame β)) given)
      ; target-compatible = constant-frame-compatible ev₁
          (MorphismFamily.target-frame α) (MorphismFamily.target-frame β) δ
          (project-frame (pair ev₀ ev₁) pr₂ ev₁ (pair-β₂ ev₀ ev₁) δ
            (endpoint-triangle α) (endpoint-triangle β) (pair-β₂ f g)
            (MorphismFamily.target-frame α) (MorphismFamily.target-frame β)
            (pair-evaluation-over₂-One ev₀ ev₁ (MorphismFamily.arrow α)
              (MorphismFamily.source-frame α) (MorphismFamily.target-frame α))
            (pair-evaluation-over₂-One ev₀ ev₁ (MorphismFamily.arrow β)
              (MorphismFamily.source-frame β) (MorphismFamily.target-frame β)) given) }

    decode-boundary-cone : {P T C : CAT Γ} (f g : MAP P C) (y : MAP T P)
      (α β : MorphismFamily (f ∘ y) (g ∘ y))
      (Φ : ConeIdentification₁
        (EndpointFiber.boundary-cone f g y α)
        (EndpointFiber.boundary-cone f g y β))
      → ConeIdentification₁.right Φ =₂ id₌ y
      → MorphismFamilyIdentification One α β
    decode-boundary-cone f g y α β Φ base-image =
      decode-endpoint-comparison α β (ConeIdentification₁.left Φ)
        (cancel-left ((pair-pre f g y) ⁻¹)
          (matching ∙
            (comp₌-assoc ((pair-pre f g y) ⁻¹) (endpoint-triangle β)
              (endpointMap _ ◁ ConeIdentification₁.left Φ)) ⁻¹))
      where
        module E = EndpointFiber f g
        matching = comp₌-unitˡ-One (Cone.match (E.boundary-cone y α)) ∙
          (comp₌-cong
            (postWhisker-id₌ (pair f g) y ∙ (postWhisker (pair f g) ◁ base-image))
            (id₌ (Cone.match (E.boundary-cone y α))) ∙
            ConeIdentification₁.compatible Φ)

  module EndpointComparison {Γ : Context} {P T C : CAT Γ}
    (f g : MAP P C) (universal : IsEquiv (EndpointFiber.base f g))
    (y : MAP T P) (α β : MorphismFamily (f ∘ y) (g ∘ y)) where
    private
      module E = EndpointFiber f g
      source-base = E.extension-base y α
      target-base = E.extension-base y β
      chosen : Fact.Factorization (postWhisker E.base) ((target-base ⁻¹) ∙ source-base)
      chosen = factor-through-postWhisker E.base universal ((target-base ⁻¹) ∙ source-base)

    cones : ConeIdentification₁ (E.boundary-cone y α) (E.boundary-cone y β)
    cones = cone-compose (E.extension-image y β)
      (cone-compose (cone-action-One E.universal (Fact.factor chosen))
        (cone-inverse (E.extension-image y α)))

    base-image : ConeIdentification₁.right cones =₂ id₌ y
    base-image = comp₌-inverseʳ-One target-base ∙
      (comp₌-cong (id₌ target-base) (comp-inv-right (target-base ⁻¹) source-base) ∙
        comp₌-cong (id₌ target-base)
          (comp₌-cong (Fact.triangle chosen) (id₌ (source-base ⁻¹))))

    value : MorphismFamilyIdentification One α β
    value = decode-boundary-cone f g y α β cones base-image


  module _ {Γ : Context} where
    unconstant-frame-compatible : {P K C : CAT Γ} (π : MAP K C)
      {u v : MAP P K} {f : MAP P C}
      (a : (π ∘ u) =₁ f) (b : (π ∘ v) =₁ f) (δ : u =₁ v)
      → (const b ∙ (π ◁ δ)) =₁ const a
      → CompatibleOver π a b δ
    unconstant-frame-compatible π a b δ given = const-One a ∙
      (given ∙ comp₌-cong ((const-One b) ⁻¹) (id₌ (π ◁ δ)))

    retarget-comparison-reflect : {P C : CAT Γ} {f g f′ g′ : MAP P C}
      (α β : MorphismFamily f g) (p : f =₁ f′) (q : g =₁ g′)
      → MorphismFamilyIdentification One (retarget-family α p q) (retarget-family β p q)
      → MorphismFamilyIdentification One α β
    retarget-comparison-reflect α β p q Φ = record
      { identification = δ
      ; source-compatible = constant-frame-compatible ev₀
          (MorphismFamily.source-frame α) (MorphismFamily.source-frame β) δ
          (cancel-left p
            (unconstant-frame-compatible ev₀
              (p ∙ MorphismFamily.source-frame α) (p ∙ MorphismFamily.source-frame β) δ
              (MorphismFamilyIdentification.source-compatible Φ) ∙
              (comp₌-assoc p (MorphismFamily.source-frame β) (ev₀ ◁ δ)) ⁻¹))
      ; target-compatible = constant-frame-compatible ev₁
          (MorphismFamily.target-frame α) (MorphismFamily.target-frame β) δ
          (cancel-left q
            (unconstant-frame-compatible ev₁
              (q ∙ MorphismFamily.target-frame α) (q ∙ MorphismFamily.target-frame β) δ
              (MorphismFamilyIdentification.target-compatible Φ) ∙
              (comp₌-assoc q (MorphismFamily.target-frame β) (ev₁ ◁ δ)) ⁻¹)) }
      where δ = MorphismFamilyIdentification.identification Φ

    initial-comparison : {P C : CAT Γ} (x : MAP One C) → IsInitial x
      → (y : MAP P C) (α β : MorphismFamily (const x) y)
      → MorphismFamilyIdentification One α β
    initial-comparison {C = C} x e y α β = retarget-comparison-reflect α β p q
      (EndpointComparison.value (const x) (id C) e y
        (retarget-family α p q) (retarget-family β p q))
      where
        p = (const-pre x y) ⁻¹
        q = (comp-unitˡ y) ⁻¹

    terminal-comparison : {P C : CAT Γ} (x : MAP One C) → IsTerminal x
      → (y : MAP P C) (α β : MorphismFamily y (const x))
      → MorphismFamilyIdentification One α β
    terminal-comparison {C = C} x e y α β = retarget-comparison-reflect α β p q
      (EndpointComparison.value (id C) (const x) e y
        (retarget-family α p q) (retarget-family β p q))
      where
        p = (comp-unitˡ y) ⁻¹
        q = (const-pre x y) ⁻¹

    initial-point-comparison : {C : CAT Γ} (x : MAP One C) → IsInitial x
      → (y : MAP One C) (α β : MorphismFamily x y)
      → MorphismFamilyIdentification One α β
    initial-point-comparison x e y α β = retarget-comparison-reflect α β p (id₌ y)
      (initial-comparison x e y
        (retarget-family α p (id₌ y)) (retarget-family β p (id₌ y)))
      where p = (const-One x) ⁻¹

    terminal-point-comparison : {C : CAT Γ} (x : MAP One C) → IsTerminal x
      → (y : MAP One C) (α β : MorphismFamily y x)
      → MorphismFamilyIdentification One α β
    terminal-point-comparison x e y α β = retarget-comparison-reflect α β (id₌ y) q
      (terminal-comparison x e y
        (retarget-family α (id₌ y) q) (retarget-family β (id₌ y) q))
      where q = (const-One x) ⁻¹


private
  module _ {Γ : Context} where
    compose-family-identification : {P C : CAT Γ} {f g : MAP P C}
      {α β γ : MorphismFamily f g}
      → MorphismFamilyIdentification One β γ → MorphismFamilyIdentification One α β
      → MorphismFamilyIdentification One α γ
    compose-family-identification {γ = γ} Ψ Φ = record
      { identification = ψ ∙ φ
      ; source-compatible = MorphismFamilyIdentification.source-compatible Φ ∙
          (comp₌-cong (MorphismFamilyIdentification.source-compatible Ψ) (id₌ (ev₀ ◁ φ)) ∙
            project-composite ev₀ ψ φ (const (MorphismFamily.source-frame γ)))
      ; target-compatible = MorphismFamilyIdentification.target-compatible Φ ∙
          (comp₌-cong (MorphismFamilyIdentification.target-compatible Ψ) (id₌ (ev₁ ◁ φ)) ∙
            project-composite ev₁ ψ φ (const (MorphismFamily.target-frame γ))) }
      where
        ψ = MorphismFamilyIdentification.identification Ψ
        φ = MorphismFamilyIdentification.identification Φ

    inverse-family-identification : {P C : CAT Γ} {f g : MAP P C}
      {α β : MorphismFamily f g}
      → MorphismFamilyIdentification One α β → MorphismFamilyIdentification One β α
    inverse-family-identification {α = α} {β} Φ = record
      { identification = δ ⁻¹
      ; source-compatible = constant-frame-compatible ev₀
          (MorphismFamily.source-frame β) (MorphismFamily.source-frame α) (δ ⁻¹)
          (compatible-inverse ev₀ (MorphismFamily.source-frame α) (MorphismFamily.source-frame β) δ
            (unconstant-frame-compatible ev₀ _ _ δ
              (MorphismFamilyIdentification.source-compatible Φ)))
      ; target-compatible = constant-frame-compatible ev₁
          (MorphismFamily.target-frame β) (MorphismFamily.target-frame α) (δ ⁻¹)
          (compatible-inverse ev₁ (MorphismFamily.target-frame α) (MorphismFamily.target-frame β) δ
            (unconstant-frame-compatible ev₁ _ _ δ
              (MorphismFamilyIdentification.target-compatible Φ))) }
      where δ = MorphismFamilyIdentification.identification Φ

    name-evaluation : {I C : CAT Γ} (h : MAP I C) (a : MAP One I)
      → (evAt a ∘ funName h) =₁ (h ∘ a)
    name-evaluation h a =
      (h ◁ (const-One a ∙ pair-β₂ (id One) (const a))) ∙
        (comp-assoc (insert a) pr₂ h ∙
          AtPoint.curry-image a (h ∘ pr₂))

module _ {Γ : Context} where
  vertex₀-family : MorphismFamily (zero {Γ = Γ}) zero
  vertex₀-family = record
    { arrow = vertex₀
    ; source-frame = const-One zero ∙ (const-pre zero zero ∙ name-evaluation (const zero) zero)
    ; target-frame = const-One zero ∙ (const-pre zero one ∙ name-evaluation (const zero) one) }
  vertex₁-family : MorphismFamily (zero {Γ = Γ}) one
  vertex₁-family = record
    { arrow = vertex₁
    ; source-frame = comp-unitˡ zero ∙ name-evaluation (id [1]) zero
    ; target-frame = comp-unitˡ one ∙ name-evaluation (id [1]) one }
  vertex₂-family : MorphismFamily (one {Γ = Γ}) one
  vertex₂-family = record
    { arrow = vertex₂
    ; source-frame = const-One one ∙ (const-pre one zero ∙ name-evaluation (const one) zero)
    ; target-frame = const-One one ∙ (const-pre one one ∙ name-evaluation (const one) one) }

private
  module _ {Γ : Context} where
    diagonal-family : MorphismFamily (id ([1] {Γ = Γ})) (id [1])
    diagonal-family = record
      { arrow = d₁; source-frame = s₀-d₁; target-frame = s₁-d₁ }

module _ {Γ : Context} where
  module MiddleVertex where
    before after : MorphismFamily (zero {Γ = Γ}) one
    before = retarget-family (restrict-family maximum zero)
      (comp-unitˡ zero) (const-One one ∙ const-pre one zero)
    after = retarget-family (restrict-family minimum one)
      (const-One zero ∙ const-pre zero one) (comp-unitˡ one)

    before-vertex : MorphismFamilyIdentification One before vertex₁-family
    before-vertex = initial-point-comparison zero interval-zero-initial one before vertex₁-family
    after-vertex : MorphismFamilyIdentification One after vertex₁-family
    after-vertex = initial-point-comparison zero interval-zero-initial one after vertex₁-family
    comparison : MorphismFamilyIdentification One before after
    comparison = compose-family-identification
      (inverse-family-identification after-vertex) before-vertex
    value : (d₀ ∘ zero) =₁ (d₂ ∘ one)
    value = MorphismFamilyIdentification.identification comparison
    source-compatible :
      (MorphismFamily.source-frame after ∙ (ev₀ ◁ value)) =₂ MorphismFamily.source-frame before
    source-compatible = unconstant-frame-compatible ev₀ _ _ value
      (MorphismFamilyIdentification.source-compatible comparison)
    target-compatible :
      (MorphismFamily.target-frame after ∙ (ev₁ ◁ value)) =₂ MorphismFamily.target-frame before
    target-compatible = unconstant-frame-compatible ev₁ _ _ value
      (MorphismFamilyIdentification.target-compatible comparison)

  module BottomVertex where
    before after : MorphismFamily (zero {Γ = Γ}) zero
    before = retarget-family (restrict-family diagonal-family zero)
      (comp-unitˡ zero) (comp-unitˡ zero)
    after = retarget-family (restrict-family minimum zero)
      (const-One zero ∙ const-pre zero zero) (comp-unitˡ zero)

    before-vertex : MorphismFamilyIdentification One before vertex₀-family
    before-vertex = initial-point-comparison zero interval-zero-initial zero before vertex₀-family
    after-vertex : MorphismFamilyIdentification One after vertex₀-family
    after-vertex = initial-point-comparison zero interval-zero-initial zero after vertex₀-family
    comparison : MorphismFamilyIdentification One before after
    comparison = compose-family-identification
      (inverse-family-identification after-vertex) before-vertex
    value : (d₁ ∘ zero) =₁ (d₂ ∘ zero)
    value = MorphismFamilyIdentification.identification comparison
    source-compatible :
      (MorphismFamily.source-frame after ∙ (ev₀ ◁ value)) =₂ MorphismFamily.source-frame before
    source-compatible = unconstant-frame-compatible ev₀ _ _ value
      (MorphismFamilyIdentification.source-compatible comparison)
    target-compatible :
      (MorphismFamily.target-frame after ∙ (ev₁ ◁ value)) =₂ MorphismFamily.target-frame before
    target-compatible = unconstant-frame-compatible ev₁ _ _ value
      (MorphismFamilyIdentification.target-compatible comparison)

  module TopVertex where
    before after : MorphismFamily (one {Γ = Γ}) one
    before = retarget-family (restrict-family maximum one)
      (comp-unitˡ one) (const-One one ∙ const-pre one one)
    after = retarget-family (restrict-family diagonal-family one)
      (comp-unitˡ one) (comp-unitˡ one)

    before-vertex : MorphismFamilyIdentification One before vertex₂-family
    before-vertex = terminal-point-comparison one interval-one-terminal one before vertex₂-family
    after-vertex : MorphismFamilyIdentification One after vertex₂-family
    after-vertex = terminal-point-comparison one interval-one-terminal one after vertex₂-family
    comparison : MorphismFamilyIdentification One before after
    comparison = compose-family-identification
      (inverse-family-identification after-vertex) before-vertex
    value : (d₀ ∘ one) =₁ (d₁ ∘ one)
    value = MorphismFamilyIdentification.identification comparison
    source-compatible :
      (MorphismFamily.source-frame after ∙ (ev₀ ◁ value)) =₂ MorphismFamily.source-frame before
    source-compatible = unconstant-frame-compatible ev₀ _ _ value
      (MorphismFamilyIdentification.source-compatible comparison)
    target-compatible :
      (MorphismFamily.target-frame after ∙ (ev₁ ◁ value)) =₂ MorphismFamily.target-frame before
    target-compatible = unconstant-frame-compatible ev₁ _ _ value
      (MorphismFamilyIdentification.target-compatible comparison)

  face-middle : (d₀ ∘ (zero {Γ = Γ})) =₁ (d₂ ∘ one)
  face-middle = MiddleVertex.value
  face-bottom : (d₁ ∘ (zero {Γ = Γ})) =₁ (d₂ ∘ zero)
  face-bottom = BottomVertex.value
  face-top : (d₀ ∘ (one {Γ = Γ})) =₁ (d₁ ∘ one)
  face-top = TopVertex.value

  d₂-zero : (d₂ ∘ (zero {Γ = Γ})) =₁ vertex₀
  d₂-zero = MorphismFamilyIdentification.identification BottomVertex.after-vertex
  d₁-zero : (d₁ ∘ (zero {Γ = Γ})) =₁ vertex₀
  d₁-zero = MorphismFamilyIdentification.identification BottomVertex.before-vertex
  d₂-one : (d₂ ∘ (one {Γ = Γ})) =₁ vertex₁
  d₂-one = MorphismFamilyIdentification.identification MiddleVertex.after-vertex
  d₀-zero : (d₀ ∘ (zero {Γ = Γ})) =₁ vertex₁
  d₀-zero = MorphismFamilyIdentification.identification MiddleVertex.before-vertex
  d₀-one : (d₀ ∘ (one {Γ = Γ})) =₁ vertex₂
  d₀-one = MorphismFamilyIdentification.identification TopVertex.before-vertex
  d₁-one : (d₁ ∘ (one {Γ = Γ})) =₁ vertex₂
  d₁-one = MorphismFamilyIdentification.identification TopVertex.after-vertex

  s₀-vertex₀ : (s₀ ∘ (vertex₀ {Γ = Γ})) =₁ zero
  s₀-vertex₀ = MorphismFamily.source-frame vertex₀-family
  s₁-vertex₀ : (s₁ ∘ (vertex₀ {Γ = Γ})) =₁ zero
  s₁-vertex₀ = MorphismFamily.target-frame vertex₀-family
  s₀-vertex₁ : (s₀ ∘ (vertex₁ {Γ = Γ})) =₁ zero
  s₀-vertex₁ = MorphismFamily.source-frame vertex₁-family
  s₁-vertex₁ : (s₁ ∘ (vertex₁ {Γ = Γ})) =₁ one
  s₁-vertex₁ = MorphismFamily.target-frame vertex₁-family
  s₀-vertex₂ : (s₀ ∘ (vertex₂ {Γ = Γ})) =₁ one
  s₀-vertex₂ = MorphismFamily.source-frame vertex₂-family
  s₁-vertex₂ : (s₁ ∘ (vertex₂ {Γ = Γ})) =₁ one
  s₁-vertex₂ = MorphismFamily.target-frame vertex₂-family

```

The six face-to-vertex comparisons retain both endpoint equations in
MiddleVertex, BottomVertex and TopVertex. Their composites through the
named vertices choose the three common-face comparisons. Together with
the six evaluations of the named vertices, these are the twelve vertex
identifications compatible with the six face-degeneracy equations.
Full triangle restriction over C³ remains a subsequent construction.

Two concrete square-coordinate consumers use the same chosen framed
uniqueness proofs. These public aliases retain both endpoint compatibilities
and add no new comparison or uniqueness choice.

```agda
module _ {Γ : Context} where
  initial-family-comparison : {P C : CAT Γ} (x : MAP One C) → IsInitial x
    → (y : MAP P C) (α β : MorphismFamily (const x) y)
    → MorphismFamilyIdentification One α β
  initial-family-comparison = initial-comparison

  terminal-family-comparison : {P C : CAT Γ} (x : MAP One C) → IsTerminal x
    → (y : MAP P C) (α β : MorphismFamily y (const x))
    → MorphismFamilyIdentification One α β
  terminal-family-comparison = terminal-comparison
```
