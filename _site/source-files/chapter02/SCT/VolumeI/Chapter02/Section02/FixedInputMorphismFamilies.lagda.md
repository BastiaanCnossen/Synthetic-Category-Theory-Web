# Framed families for fixed-input functors

Endpoint changes retain their full compatibility equations. Fixing one input
of a product action agrees with pairing the variable family and the chosen
identity family. Transfer then compares that action with a specified unary
functor. These constructions are used by both natural-transformation whiskerings.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.FixedInputMorphismFamilies where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (terminate; module Constructions)
open Constructions using (const; terminal-identification)
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-assoc; comp-unitˡ; comp-unitʳ; postWhisker-id₌; preWhisker-id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (comp₌-assoc; comp₌-cong; inv-comp-right; comp-inv-left; postWhisker-comp₌; preWhisker-comp₌)
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (contractible-unique; terminal-unique₂)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (cancel-left; comp₌-unitʳ-One; comp₌-unitˡ-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (post-triangle)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence using (left-unitor-comp; postWhisker-id-One)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun)
open import SCT.VolumeI.Chapter01.Section07.FunctorProperties using (funTerminal-isEquiv)
open import SCT.VolumeI.Chapter01.Section07.Currying using (funUncurry)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPost)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1]; zero; one)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (Ar; ev₀; ev₁; evAt; insert; MorphismFamily; MorphismFamilyIdentification; identity-family; module AtPoint)
open import SCT.VolumeI.Chapter02.Section01.MorphismFunctor using (map-morphism-family; evAt-post)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyOperations using (retarget-family; retarget-family-comparison; family-comparison; module FamilyComparison)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyComparisons using (compose-family-comparisons; inverse-family-comparison)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyPostcomposition using (post-family-comparison)
open import SCT.VolumeI.Chapter02.Section01.IdentityFamilyPostcomposition using (post-identity-family)
open import SCT.VolumeI.Chapter02.Section01.IdentityFamilyTransport using (module IdentityFamilyChange)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyPostcompositionPasting using (module Pasting; module Image; module ReflectedFrames)
open import SCT.VolumeI.Chapter02.Section02.ProductMorphismFamilies using (pair-morphism-family; product-family-reflect; module ProductFamily)

module _ {Γ : Context} where
  same-arrow : {P C : CAT Γ} {x y : MAP P C} (h : MAP P (Ar C))
    (p p′ : (ev₀ ∘ h) =₁ x) (q q′ : (ev₁ ∘ h) =₁ y) → p′ =₂ p → q′ =₂ q →
    MorphismFamilyIdentification One (record { arrow = h ; source-frame = p ; target-frame = q })
      (record { arrow = h ; source-frame = p′ ; target-frame = q′ })
  same-arrow h p p′ q q′ source target = family-comparison _ _ (id₌ h)
    (source ∙ (comp₌-unitʳ-One p′ ∙ comp₌-cong (id₌ p′) (postWhisker-id₌ ev₀ h)))
    (target ∙ (comp₌-unitʳ-One q′ ∙ comp₌-cong (id₌ q′) (postWhisker-id₌ ev₁ h)))

  retarget-assoc : {P C : CAT Γ} {x y x′ y′ x″ y″ : MAP P C}
    (f : MorphismFamily x y) (a : x =₁ x′) (b : y =₁ y′) (p : x′ =₁ x″) (q : y′ =₁ y″) →
    MorphismFamilyIdentification One (retarget-family (retarget-family f a b) p q)
      (retarget-family f (p ∙ a) (q ∙ b))
  retarget-assoc f a b p q = same-arrow (MorphismFamily.arrow f) _ _ _ _
    (comp₌-assoc p a (MorphismFamily.source-frame f)) (comp₌-assoc q b (MorphismFamily.target-frame f))

  retarget-cong : {P C : CAT Γ} {x y x′ y′ : MAP P C} (f : MorphismFamily x y)
    {a a′ : x =₁ x′} {b b′ : y =₁ y′} → a =₂ a′ → b =₂ b′ →
    MorphismFamilyIdentification One (retarget-family f a b) (retarget-family f a′ b′)
  retarget-cong f p q = same-arrow (MorphismFamily.arrow f) _ _ _ _
    (comp₌-cong (p ⁻¹) (id₌ (MorphismFamily.source-frame f)))
    (comp₌-cong (q ⁻¹) (id₌ (MorphismFamily.target-frame f)))

  post-retarget : {P C D : CAT Γ} (F : MAP C D) {x y x′ y′ : MAP P C}
    (f : MorphismFamily x y) (a : x =₁ x′) (b : y =₁ y′) →
    MorphismFamilyIdentification One (map-morphism-family F (retarget-family f a b))
      (retarget-family (map-morphism-family F f) (F ◁ a) (F ◁ b))
  post-retarget F f a b = same-arrow (funPost F ∘ A.arrow) _ _ _ _
    (endpoint zero A.source-frame a) (endpoint one A.target-frame b)
    where
    module A = MorphismFamily f
    endpoint : (v : MAP One ([1] {Γ = Γ})) {z z′ : MAP _ _}
      (p : (evAt v ∘ A.arrow) =₁ z) (q : z =₁ z′) →
      ((F ◁ q) ∙ ((F ◁ p) ∙ (comp-assoc A.arrow (evAt v) F ∙
        ((evAt-post v F ▷ A.arrow) ∙ (comp-assoc A.arrow (funPost F) (evAt v)) ⁻¹)))) =₂
      ((F ◁ (q ∙ p)) ∙ (comp-assoc A.arrow (evAt v) F ∙
        ((evAt-post v F ▷ A.arrow) ∙ (comp-assoc A.arrow (funPost F) (evAt v)) ⁻¹)))
    endpoint v p q = comp₌-cong ((postWhisker-comp₌ F q p) ⁻¹) (id₌ tail) ∙
      (comp₌-assoc (F ◁ q) (F ◁ p) tail) ⁻¹
      where tail = comp-assoc A.arrow (evAt v) F ∙
              ((evAt-post v F ▷ A.arrow) ∙ (comp-assoc A.arrow (funPost F) (evAt v)) ⁻¹)

  retarget-reflect : {P C : CAT Γ} {x y x′ y′ : MAP P C}
    {f g : MorphismFamily x y} (p : x =₁ x′) (q : y =₁ y′) →
    MorphismFamilyIdentification One (retarget-family f p q) (retarget-family g p q) →
    MorphismFamilyIdentification One f g
  retarget-reflect {f = f} {g} p q given = family-comparison f g A.identification
    (cancel-left p (A.source ∙ (comp₌-assoc p (MorphismFamily.source-frame g) (ev₀ ◁ A.identification)) ⁻¹))
    (cancel-left q (A.target ∙ (comp₌-assoc q (MorphismFamily.target-frame g) (ev₁ ◁ A.identification)) ⁻¹))
    where module A = FamilyComparison given

  pair-family-comparison : {P C D : CAT Γ} {x₁ y₁ : MAP P C} {x₂ y₂ : MAP P D}
    {f f′ : MorphismFamily x₁ y₁} {g g′ : MorphismFamily x₂ y₂} →
    MorphismFamilyIdentification One f f′ → MorphismFamilyIdentification One g g′ →
    MorphismFamilyIdentification One (pair-morphism-family f g) (pair-morphism-family f′ g′)
  pair-family-comparison {x₁ = x₁} {y₁} {x₂} {y₂} {f} {f′} {g} {g′} a b = product-family-reflect
    (retarget-reflect (pair-β₁ x₁ x₂) (pair-β₁ y₁ y₂)
      (compose-family-comparisons (inverse-family-comparison (ProductFamily.first-projection f′ g′))
        (compose-family-comparisons a (ProductFamily.first-projection f g))))
    (retarget-reflect (pair-β₂ x₁ x₂) (pair-β₂ y₁ y₂)
      (compose-family-comparisons (inverse-family-comparison (ProductFamily.second-projection f′ g′))
        (compose-family-comparisons b (ProductFamily.second-projection f g))))

  cancel-inverse-tail : {C D : CAT Γ} {f g h : MAP C D} (a : f =₁ h) (b : f =₁ g)
    → ((a ∙ b ⁻¹) ∙ b) =₂ a
  cancel-inverse-tail = inv-comp-right

  post-id : {P C : CAT Γ} {x y : MAP P C} (f : MorphismFamily x y) →
    MorphismFamilyIdentification One (retarget-family (map-morphism-family (id C) f) (comp-unitˡ x) (comp-unitˡ y)) f
  post-id {P = P} {C} {x} {y} f = ReflectedFrames.value mapped f U theta (id₌ U) p q
    (mapped-image zero p (MorphismFamily.source-frame M.family) M.first-image)
    (mapped-image one q (MorphismFamily.target-frame M.family) M.last-image)
    (base-image zero A.source-frame) (base-image one A.target-frame)
    where
    module A = MorphismFamily f
    U = funUncurry A.arrow
    base : (v : MAP One ([1] {Γ = Γ})) {z : MAP P C} → (evAt v ∘ A.arrow) =₁ z → (U ∘ insert v) =₁ z
    base v frame = frame ∙ (AtPoint.uncurry-image v A.arrow) ⁻¹
    base-image : (v : MAP One ([1] {Γ = Γ})) {z : MAP P C} (frame : (evAt v ∘ A.arrow) =₁ z) →
      (base v frame ∙ ((id₌ U ▷ insert v) ∙ AtPoint.uncurry-image v A.arrow)) =₂ frame
    base-image v frame = inv-comp-right frame (AtPoint.uncurry-image v A.arrow) ∙
      comp₌-cong (id₌ (base v frame)) (comp₌-unitˡ-One (AtPoint.uncurry-image v A.arrow) ∙
        comp₌-cong (preWhisker-id₌ U (insert v)) (id₌ (AtPoint.uncurry-image v A.arrow)))
    p = base zero A.source-frame
    q = base one A.target-frame
    module M = Image (id C) f U (id₌ U) p q (base-image zero A.source-frame) (base-image one A.target-frame)
    mapped = retarget-family M.family (comp-unitˡ x) (comp-unitˡ y)
    theta = comp-unitˡ U ∙ M.representation
    mapped-image : (v : MAP One ([1] {Γ = Γ})) {z : MAP P C}
      (r : (U ∘ insert v) =₁ z)
      (frame : (evAt v ∘ MorphismFamily.arrow M.family) =₁ (id C ∘ z))
      → (post-triangle (id C) U (insert v) r ∙
          ((M.representation ▷ insert v) ∙ AtPoint.uncurry-image v (MorphismFamily.arrow M.family))) =₂ frame
      → (r ∙ ((theta ▷ insert v) ∙ AtPoint.uncurry-image v (MorphismFamily.arrow mapped))) =₂
          (comp-unitˡ z ∙ frame)
    mapped-image v r frame given = comp₌-cong (id₌ (comp-unitˡ _)) given ∙
      (comp₌-assoc (comp-unitˡ _) triangle tail ∙
        (comp₌-cong compatible (id₌ tail) ∙
          ((comp₌-assoc r (comp-unitˡ U ▷ i) tail) ⁻¹ ∙
            comp₌-cong (id₌ r)
              (comp₌-assoc (comp-unitˡ U ▷ i) (M.representation ▷ i) mu ∙
                comp₌-cong (preWhisker-comp₌ (comp-unitˡ U) M.representation i) (id₌ mu)))))
      where
      i = insert {P = P} v
      mu = AtPoint.uncurry-image v (MorphismFamily.arrow mapped)
      tail = (M.representation ▷ i) ∙ mu
      triangle = post-triangle (id C) U i r
      compatible : (r ∙ (comp-unitˡ U ▷ i)) =₂ (comp-unitˡ _ ∙ triangle)
      compatible = comp₌-assoc (comp-unitˡ _) (id C ◁ r) (comp-assoc i U (id C)) ∙
        (comp₌-cong ((postWhisker-id-One r) ⁻¹) (id₌ (comp-assoc i U (id C))) ∙
          ((comp₌-assoc r (comp-unitˡ (U ∘ i)) (comp-assoc i U (id C))) ⁻¹ ∙
            comp₌-cong (id₌ r) ((left-unitor-comp i U) ⁻¹)))

  retarget-comparison : {P C : CAT Γ} {x y x′ y′ : MAP P C} {f g : MorphismFamily x y}
    → MorphismFamilyIdentification One f g → (p : x =₁ x′) (q : y =₁ y′)
    → MorphismFamilyIdentification One (retarget-family f p q) (retarget-family g p q)
  retarget-comparison given p q = retarget-family-comparison p q given

  terminal-family-unique : {P : CAT Γ} {x y : MAP P One} (f g : MorphismFamily x y)
    → MorphismFamilyIdentification One f g
  terminal-family-unique f g = family-comparison f g
    (contractible-unique (funTerminal-isEquiv [1]) (MorphismFamily.arrow f) (MorphismFamily.arrow g))
    (terminal-unique₂ _ _) (terminal-unique₂ _ _)

  module ConstantChange {P C D : CAT Γ} (y : MAP One D) (x : MAP P C) where
    rho : (y ∘ (terminate C ∘ x)) =₁ (const y ∘ x)
    rho = (id₌ (const y) ▷ x) ∙ (comp-assoc x (terminate C) y) ⁻¹
    tau : (terminate C ∘ x) =₁ terminate P
    tau = terminal-identification _ _
    frame : (const y ∘ x) =₁ const y
    frame = (y ◁ tau) ∙ rho ⁻¹

  module ConstantImage {P C D : CAT Γ} (y : MAP One D) {x x′ : MAP P C} (f : MorphismFamily x x′) where
    private
      module Source = ConstantChange y x using (frame; rho; tau)
      module Target = ConstantChange y x′ using (frame; rho; tau)
      module Paste = Pasting (terminate C) y (const y) (id₌ (const y)) f using (comparison)
      terminal-family = map-morphism-family (terminate C) f
      double = map-morphism-family y terminal-family
      adjusted = retarget-family terminal-family Source.tau Target.tau
      reduced : MorphismFamilyIdentification One
        (retarget-family double (y ◁ Source.tau) (y ◁ Target.tau)) (identity-family (const y))
      reduced = compose-family-comparisons (post-identity-family y (terminate P))
        (compose-family-comparisons (post-family-comparison y (terminal-family-unique adjusted (identity-family (terminate P))))
          (inverse-family-comparison (post-retarget y terminal-family Source.tau Target.tau)))
    comparison : MorphismFamilyIdentification One
      (retarget-family (map-morphism-family (const y) f) Source.frame Target.frame) (identity-family (const y))
    comparison = compose-family-comparisons reduced
      (compose-family-comparisons
        (retarget-cong double (cancel-inverse-tail (y ◁ Source.tau) Source.rho) (cancel-inverse-tail (y ◁ Target.tau) Target.rho))
        (compose-family-comparisons (retarget-assoc double Source.rho Target.rho Source.frame Target.frame)
          (inverse-family-comparison (retarget-comparison Paste.comparison Source.frame Target.frame))))

  point-frame : {D : CAT Γ} (y : MAP One D) → const {P = One} y =₁ y
  point-frame y = comp-unitʳ y ∙ (y ◁ terminal-identification {Γ = Γ} (terminate One) (id One))
  constant-point-frame : {C D : CAT Γ} (y : MAP One D) (x : MAP One C) → (const y ∘ x) =₁ y
  constant-point-frame y x = point-frame y ∙ ConstantChange.frame y x

  module ConstantAbsolute {C D : CAT Γ} (y : MAP One D) {x x′ : MAP One C} (f : MorphismFamily x x′) where
    comparison : MorphismFamilyIdentification One
      (retarget-family (map-morphism-family (const y) f) (constant-point-frame y x) (constant-point-frame y x′)) (identity-family y)
    comparison = compose-family-comparisons (IdentityFamilyChange.value (point-frame y))
      (compose-family-comparisons (retarget-comparison (ConstantImage.comparison y f) (point-frame y) (point-frame y))
        (inverse-family-comparison (retarget-assoc (map-morphism-family (const y) f)
          (ConstantChange.frame y x) (ConstantChange.frame y x′) (point-frame y) (point-frame y))))


  module Pairing {P A B C : CAT Γ} (J : MAP A (B × C)) {x y : MAP P A} (f : MorphismFamily x y)
    {x₁ y₁ : MAP P B} {x₂ y₂ : MAP P C} (g : MorphismFamily x₁ y₁) (h : MorphismFamily x₂ y₂)
    (p₁ : (pr₁ ∘ (J ∘ x)) =₁ x₁) (q₁ : (pr₁ ∘ (J ∘ y)) =₁ y₁)
    (p₂ : (pr₂ ∘ (J ∘ x)) =₁ x₂) (q₂ : (pr₂ ∘ (J ∘ y)) =₁ y₂)
    (first : MorphismFamilyIdentification One (retarget-family (map-morphism-family pr₁ (map-morphism-family J f)) p₁ q₁) g)
    (second : MorphismFamilyIdentification One (retarget-family (map-morphism-family pr₂ (map-morphism-family J f)) p₂ q₂) h) where
    source-frame : (J ∘ x) =₁ pair x₁ x₂
    source-frame = pair₌ ((pair-β₁ x₁ x₂) ⁻¹ ∙ p₁) ((pair-β₂ x₁ x₂) ⁻¹ ∙ p₂)
    target-frame : (J ∘ y) =₁ pair y₁ y₂
    target-frame = pair₌ ((pair-β₁ y₁ y₂) ⁻¹ ∙ q₁) ((pair-β₂ y₁ y₂) ⁻¹ ∙ q₂)
    value = retarget-family (map-morphism-family J f) source-frame target-frame
    module Paired = ProductFamily g h
      using (first-projection; second-projection)

    module Projection where
      abstract
        comparison : {Y : CAT Γ} (π : MAP (B × C) Y) {u v : MAP P Y}
          (s : (π ∘ pair x₁ x₂) =₁ u) (t : (π ∘ pair y₁ y₂) =₁ v)
          (p : (π ∘ (J ∘ x)) =₁ u) (q : (π ∘ (J ∘ y)) =₁ v)
          (source : (s ∙ (π ◁ source-frame)) =₂ p) (target : (t ∙ (π ◁ target-frame)) =₂ q)
          (k : MorphismFamily u v)
          (result : MorphismFamilyIdentification One (retarget-family (map-morphism-family π (map-morphism-family J f)) p q) k)
          (paired : MorphismFamilyIdentification One (retarget-family (map-morphism-family π (pair-morphism-family g h)) s t) k) →
          MorphismFamilyIdentification One (map-morphism-family π value) (map-morphism-family π (pair-morphism-family g h))
        comparison π s t p q source target k result paired = retarget-reflect s t
          (compose-family-comparisons (inverse-family-comparison paired)
            (compose-family-comparisons result
              (compose-family-comparisons (retarget-cong (map-morphism-family π (map-morphism-family J f)) source target)
                (compose-family-comparisons
                  (retarget-assoc (map-morphism-family π (map-morphism-family J f)) (π ◁ source-frame) (π ◁ target-frame) s t)
                  (retarget-comparison (post-retarget π (map-morphism-family J f) source-frame target-frame) s t)))))

    abstract
      comparison : MorphismFamilyIdentification One value (pair-morphism-family g h)
      comparison = product-family-reflect
        (Projection.comparison pr₁ (pair-β₁ x₁ x₂) (pair-β₁ y₁ y₂) p₁ q₁
          (comp-inv-left (pair-β₁ x₁ x₂) p₁ ∙ comp₌-cong (id₌ (pair-β₁ x₁ x₂))
            (pair₌-β₁ ((pair-β₁ x₁ x₂) ⁻¹ ∙ p₁) ((pair-β₂ x₁ x₂) ⁻¹ ∙ p₂)))
          (comp-inv-left (pair-β₁ y₁ y₂) q₁ ∙ comp₌-cong (id₌ (pair-β₁ y₁ y₂))
            (pair₌-β₁ ((pair-β₁ y₁ y₂) ⁻¹ ∙ q₁) ((pair-β₂ y₁ y₂) ⁻¹ ∙ q₂)))
          g first Paired.first-projection)
        (Projection.comparison pr₂ (pair-β₂ x₁ x₂) (pair-β₂ y₁ y₂) p₂ q₂
          (comp-inv-left (pair-β₂ x₁ x₂) p₂ ∙ comp₌-cong (id₌ (pair-β₂ x₁ x₂))
            (pair₌-β₂ ((pair-β₁ x₁ x₂) ⁻¹ ∙ p₁) ((pair-β₂ x₁ x₂) ⁻¹ ∙ p₂)))
          (comp-inv-left (pair-β₂ y₁ y₂) q₂ ∙ comp₌-cong (id₌ (pair-β₂ y₁ y₂))
            (pair₌-β₂ ((pair-β₁ y₁ y₂) ⁻¹ ∙ q₁) ((pair-β₂ y₁ y₂) ⁻¹ ∙ q₂)))
          h second Paired.second-projection)

  module FixRight {A B : CAT Γ} (y : MAP One B) where
    insertion : MAP A (A × B)
    insertion = pair (id A) (const y)
    identity-comparison = pair-β₁ (id A) (const y)
    constant-comparison = pair-β₂ (id A) (const y)
    identity-frame : (x : MAP One A) → (pr₁ ∘ (insertion ∘ x)) =₁ x
    identity-frame x = comp-unitˡ x ∙ ((identity-comparison ▷ x) ∙ (comp-assoc x insertion pr₁) ⁻¹)
    constant-frame : (x : MAP One A) → (pr₂ ∘ (insertion ∘ x)) =₁ y
    constant-frame x = constant-point-frame y x ∙ ((constant-comparison ▷ x) ∙ (comp-assoc x insertion pr₂) ⁻¹)
    frame : (x : MAP One A) → (insertion ∘ x) =₁ pair x y
    frame x = pair₌ ((pair-β₁ x y) ⁻¹ ∙ identity-frame x) ((pair-β₂ x y) ⁻¹ ∙ constant-frame x)

    module Arrow {x x′ : MAP One A} (f : MorphismFamily x x′) where
      module First = Pasting insertion pr₁ (id A) identity-comparison f
        using (comparison; source-change; target-change)
      module Second = Pasting insertion pr₂ (const y) constant-comparison f
        using (comparison; source-change; target-change)
      first : MorphismFamilyIdentification One
        (retarget-family (map-morphism-family pr₁ (map-morphism-family insertion f)) (identity-frame x) (identity-frame x′)) f
      first = compose-family-comparisons (post-id f)
        (compose-family-comparisons (retarget-comparison First.comparison (comp-unitˡ x) (comp-unitˡ x′))
          (inverse-family-comparison (retarget-assoc (map-morphism-family pr₁ (map-morphism-family insertion f))
            First.source-change First.target-change (comp-unitˡ x) (comp-unitˡ x′))))
      second : MorphismFamilyIdentification One
        (retarget-family (map-morphism-family pr₂ (map-morphism-family insertion f)) (constant-frame x) (constant-frame x′))
        (identity-family y)
      second = compose-family-comparisons (ConstantAbsolute.comparison y f)
        (compose-family-comparisons (retarget-comparison Second.comparison (constant-point-frame y x) (constant-point-frame y x′))
          (inverse-family-comparison (retarget-assoc (map-morphism-family pr₂ (map-morphism-family insertion f))
            Second.source-change Second.target-change (constant-point-frame y x) (constant-point-frame y x′))))
      module Paired = Pairing insertion f f (identity-family y)
        (identity-frame x) (identity-frame x′) (constant-frame x) (constant-frame x′) first second
        using (comparison)
      abstract
        comparison : MorphismFamilyIdentification One (retarget-family (map-morphism-family insertion f) (frame x) (frame x′))
          (pair-morphism-family f (identity-family y))
        comparison = Paired.comparison

  module FixLeft {A B : CAT Γ} (x : MAP One A) where
    insertion : MAP B (A × B)
    insertion = pair (const x) (id B)
    constant-comparison = pair-β₁ (const x) (id B)
    identity-comparison = pair-β₂ (const x) (id B)
    constant-frame : (y : MAP One B) → (pr₁ ∘ (insertion ∘ y)) =₁ x
    constant-frame y = constant-point-frame x y ∙ ((constant-comparison ▷ y) ∙ (comp-assoc y insertion pr₁) ⁻¹)
    identity-frame : (y : MAP One B) → (pr₂ ∘ (insertion ∘ y)) =₁ y
    identity-frame y = comp-unitˡ y ∙ ((identity-comparison ▷ y) ∙ (comp-assoc y insertion pr₂) ⁻¹)
    frame : (y : MAP One B) → (insertion ∘ y) =₁ pair x y
    frame y = pair₌ ((pair-β₁ x y) ⁻¹ ∙ constant-frame y) ((pair-β₂ x y) ⁻¹ ∙ identity-frame y)

    module Arrow {y y′ : MAP One B} (f : MorphismFamily y y′) where
      module First = Pasting insertion pr₁ (const x) constant-comparison f
        using (comparison; source-change; target-change)
      module Second = Pasting insertion pr₂ (id B) identity-comparison f
        using (comparison; source-change; target-change)
      first : MorphismFamilyIdentification One
        (retarget-family (map-morphism-family pr₁ (map-morphism-family insertion f)) (constant-frame y) (constant-frame y′))
        (identity-family x)
      first = compose-family-comparisons (ConstantAbsolute.comparison x f)
        (compose-family-comparisons (retarget-comparison First.comparison (constant-point-frame x y) (constant-point-frame x y′))
          (inverse-family-comparison (retarget-assoc (map-morphism-family pr₁ (map-morphism-family insertion f))
            First.source-change First.target-change (constant-point-frame x y) (constant-point-frame x y′))))
      second : MorphismFamilyIdentification One
        (retarget-family (map-morphism-family pr₂ (map-morphism-family insertion f)) (identity-frame y) (identity-frame y′)) f
      second = compose-family-comparisons (post-id f)
        (compose-family-comparisons (retarget-comparison Second.comparison (comp-unitˡ y) (comp-unitˡ y′))
          (inverse-family-comparison (retarget-assoc (map-morphism-family pr₂ (map-morphism-family insertion f))
            Second.source-change Second.target-change (comp-unitˡ y) (comp-unitˡ y′))))
      module Paired = Pairing insertion f (identity-family x) f
        (constant-frame y) (constant-frame y′) (identity-frame y) (identity-frame y′) first second
        using (comparison)
      abstract
        comparison : MorphismFamilyIdentification One (retarget-family (map-morphism-family insertion f) (frame y) (frame y′))
          (pair-morphism-family (identity-family x) f)
        comparison = Paired.comparison

  module Transfer {A B C : CAT Γ} (K : MAP B C) (J : MAP A B) (L : MAP A C) (η : (K ∘ J) =₁ L)
    {x x′ : MAP One A} {y y′ : MAP One B} {z z′ : MAP One C}
    (f : MorphismFamily x x′) (g : MorphismFamily y y′)
    (δ : (J ∘ x) =₁ y) (δ′ : (J ∘ x′) =₁ y′)
    (κ : (K ∘ y) =₁ z) (κ′ : (K ∘ y′) =₁ z′)
    (given : MorphismFamilyIdentification One (retarget-family (map-morphism-family J f) δ δ′) g) where
    private
      module Paste = Pasting J K L η f
        using (comparison; source-change; target-change)
    double : MorphismFamily (K ∘ (J ∘ x)) (K ∘ (J ∘ x′))
    double = map-morphism-family K (map-morphism-family J f)
    source-change : (K ∘ (J ∘ x)) =₁ z
    source-change = κ ∙ (K ◁ δ)
    target-change : (K ∘ (J ∘ x′)) =₁ z′
    target-change = κ′ ∙ (K ◁ δ′)
    source-frame : (L ∘ x) =₁ z
    source-frame = source-change ∙ Paste.source-change ⁻¹
    target-frame : (L ∘ x′) =₁ z′
    target-frame = target-change ∙ Paste.target-change ⁻¹
    action : MorphismFamily z z′
    action = retarget-family (map-morphism-family L f) source-frame target-frame
    original : MorphismFamily z z′
    original = retarget-family (map-morphism-family K g) κ κ′

    abstract
      first : MorphismFamilyIdentification One (retarget-family double source-change target-change) original
      first = compose-family-comparisons (retarget-comparison (post-family-comparison K given) κ κ′)
        (compose-family-comparisons (retarget-comparison (inverse-family-comparison (post-retarget K (map-morphism-family J f) δ δ′)) κ κ′)
          (inverse-family-comparison (retarget-assoc double (K ◁ δ) (K ◁ δ′) κ κ′)))
      second : MorphismFamilyIdentification One (retarget-family double source-change target-change) action
      second = compose-family-comparisons (retarget-comparison Paste.comparison source-frame target-frame)
        (compose-family-comparisons (inverse-family-comparison (retarget-assoc double Paste.source-change Paste.target-change source-frame target-frame))
          (inverse-family-comparison (retarget-cong double (cancel-inverse-tail source-change Paste.source-change)
            (cancel-inverse-tail target-change Paste.target-change))))
      comparison : MorphismFamilyIdentification One original action
      comparison = compose-family-comparisons second (inverse-family-comparison first)

```
