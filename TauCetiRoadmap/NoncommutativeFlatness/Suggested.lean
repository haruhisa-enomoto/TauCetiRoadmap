module

import Mathlib
import TauCeti.LinearAlgebra.TensorProduct.Balanced.Basic
import TauCeti.Algebra.Category.ModuleCat.Algebra
import TauCeti.Algebra.Module.CharacterModule.MulOpposite
import TauCeti.CategoryTheory.FinitelyPresentedFunctor.Basic
import TauCeti.RingTheory.MatlisDuality.Basic
import TauCeti.RingTheory.GlobalDimension
import TauCeti.RingTheory.Jacobson.Semiperfect
import TauCeti.Algebra.Module.ProjectiveCover.Basic
import TauCeti.Algebra.Module.Projective.FinitePresentation
import TauCeti.Algebra.Module.MinimalProjectivePresentation.Basic

/-!
# Flatness and homological dimensions of noncommutative rings: target signatures

**This file is not the roadmap and is not exhaustive.** The definitive document is
`README.md`. The statements here suggest Lean forms for particular milestones, so that
contributors and reviewers converge on names and signatures; discharging all of them finishes
neither a layer nor the roadmap. `sorry` is allowed in this human-owned roadmap library -- these
are goals, not proofs.

Layers as in `README.md`: 0 modules over a preadditive category and their tensor product; 1 `Tor`
over an arbitrary ring; 2 flat modules; 3 flat dimension and weak global dimension; 4 semiperfect
and perfect rings and Bass's Theorem P.

Layer 0 is category-primary (README, "Conventions"). `C : Type u` is preadditive with
`Category.{v} C`. `ModCat C` (`Mod C`) is the full subcategory of additive functors
`Cᵒᵖ ⥤ AddCommGrpCat.{w}` (right modules), and `LeftModCat C` that of additive functors
`C ⥤ AddCommGrpCat.{w}`. For an `R`-linear `C` the `R`-structure of a module is derived: `r` acts
on `F(c)` by `F(r • 𝟙 c)`. `F ⊗_C G` is a coend in `ModuleCat R`; it exists when `C` is
`EssentiallySmall.{w}`. A ring `A` is the one-object category `SingleObj A`. Ring-level objects are
native: `M ⊗_A N` is `TauCeti.BalancedTensorProduct R A M N`, with `R`-linear maps, compared with
the categorical tensor product in 0.6.

Layers 1–4 are under review: they are to be converted to the category-primary design and are
currently stated for rings. A right `A`-module is a left `Aᵐᵒᵖ`-module and a right ideal is a
`Submodule Aᵐᵒᵖ A`. `Tor` takes values in `ModuleCat R`; Layers 2 and 3 use `R = ℤ`.
Declarations that Tau Ceti already has are referred to by their full `TauCeti.` names.

Not stated here, and specified in prose in `README.md`: the transfer lemmas of 0.2, the `ULift`ed
representables for large `C`, the `Tor` swap, the naturality of the isomorphisms, and the
acceptance checks other than those in the last section.
-/

namespace TauCetiRoadmap.NoncommutativeFlatness

open CategoryTheory CategoryTheory.Limits MulOpposite Opposite

open scoped CharacterModule DirectSum TensorProduct

universe w v u t

/-! ## Layer 0: modules over a preadditive category and their tensor product -/

/-! ### 0.1 `Mod C` -/

section ModCat

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- **0.1** `Mod C`: right `C`-modules, the additive functors `Cᵒᵖ ⥤ AddCommGrpCat`, as a full
subcategory of the functor category (Mathlib's `C ⥤+ D`). -/
abbrev ModCat := Cᵒᵖ ⥤+ AddCommGrpCat.{w}

/-- **0.1** Left `C`-modules: the additive functors `C ⥤ AddCommGrpCat`. `LeftModCat Cᵒᵖ` is
`ModCat C`. -/
abbrev LeftModCat := C ⥤+ AddCommGrpCat.{w}

section Closure

variable {D : Type u} [Category.{v} D] [Preadditive D]

/-- **0.1** The zero functor is additive. -/
instance : (additiveFunctor D AddCommGrpCat.{w}).ContainsZero := sorry

/-- **0.1** Additive functors are closed under kernels. -/
instance : (additiveFunctor D AddCommGrpCat.{w}).IsClosedUnderKernels := sorry

/-- **0.1** Additive functors are closed under cokernels. -/
instance : (additiveFunctor D AddCommGrpCat.{w}).IsClosedUnderCokernels := sorry

/-- **0.1** Additive functors are closed under finite products. -/
instance : (additiveFunctor D AddCommGrpCat.{w}).IsClosedUnderFiniteProducts := sorry

end Closure

/-- **0.1** `Mod C` is abelian, by the closure properties and Mathlib's instance for full
subcategories (`Mathlib/CategoryTheory/Abelian/Subcategory.lean`). -/
noncomputable example : Abelian (ModCat.{w} C) := inferInstance

/-- **0.1** `Mod C` has enough projectives when `C` is `w`-small. -/
instance [EssentiallySmall.{w} C] : EnoughProjectives (ModCat.{w} C) := sorry

/-- **0.1** The Yoneda embedding into `Mod C`, `X ↦ Hom(-, X)`. -/
def ModCat.yoneda : C ⥤ ModCat.{v} C :=
  ObjectProperty.lift _ preadditiveYoneda fun X ↦
    (inferInstance : (preadditiveYoneda.obj X).Additive)

/-- **0.1** The Yoneda embedding into left modules, `X ↦ Hom(X, -)`. -/
def LeftModCat.coyoneda : Cᵒᵖ ⥤ LeftModCat.{v} C :=
  ObjectProperty.lift _ preadditiveCoyoneda fun X ↦
    (inferInstance : (preadditiveCoyoneda.obj X).Additive)

/-- **0.1** Representable modules are projective. -/
instance (X : C) : Projective ((ModCat.yoneda C).obj X) := sorry

/-- **0.1** `mod C ⊆ Mod C`: Tau Ceti's finitely presented functors are additive. -/
theorem isFinitelyPresentedFunctor_le_additiveFunctor :
    TauCeti.isFinitelyPresentedFunctor C ≤ additiveFunctor Cᵒᵖ AddCommGrpCat.{v} :=
  fun _ hF ↦ hF.additive

/-- **0.1** The inclusion `mod C ⥤ Mod C`. -/
abbrev ModCat.ιFinitelyPresented :
    (TauCeti.isFinitelyPresentedFunctor C).FullSubcategory ⥤ ModCat.{v} C :=
  ObjectProperty.ιOfLE (isFinitelyPresentedFunctor_le_additiveFunctor C)

end ModCat

section Linear

variable (R : Type*) [CommRing R] {D : Type u} [Category.{v} D] [Preadditive D] [Linear R D]

/-- **0.1** The derived `R`-action on `F(d)` for an additive `F` on an `R`-linear category:
`r` acts by `F(r • 𝟙 d)`. -/
@[implicit_reducible]
def Functor.objModule (F : D ⥤ AddCommGrpCat.{w}) [F.Additive] (d : D) : Module R (F.obj d) where
  smul r x := (F.map (r • 𝟙 d)).hom x
  one_smul x := by
    change (F.map ((1 : R) • 𝟙 d)).hom x = x
    rw [one_smul, F.map_id]; rfl
  mul_smul r s x := by
    change (F.map ((r * s) • 𝟙 d)).hom x = (F.map (r • 𝟙 d)).hom ((F.map (s • 𝟙 d)).hom x)
    rw [← AddCommGrpCat.comp_apply, ← F.map_comp, Linear.smul_comp, Category.id_comp, mul_comm,
      mul_smul]
  smul_zero r := map_zero _
  smul_add r x y := map_add _ x y
  add_smul r s x := by
    change (F.map ((r + s) • 𝟙 d)).hom x = (F.map (r • 𝟙 d)).hom x + (F.map (s • 𝟙 d)).hom x
    rw [add_smul, F.map_add]; rfl
  zero_smul x := by
    change (F.map ((0 : R) • 𝟙 d)).hom x = 0
    rw [zero_smul, F.map_zero]; rfl

/-- **0.1** An additive functor to abelian groups on an `R`-linear category, with its derived
`R`-structure, as a functor to `ModuleCat R`. -/
def Functor.toModuleCat (F : D ⥤ AddCommGrpCat.{w}) [F.Additive] : D ⥤ ModuleCat.{w} R where
  obj d := letI := Functor.objModule R F d; ModuleCat.of R (F.obj d)
  map {d d'} f := letI := Functor.objModule R F d; letI := Functor.objModule R F d'
    ModuleCat.ofHom
      { toFun := (F.map f).hom
        map_add' := map_add _
        map_smul' r x := by
          change (F.map f).hom ((F.map (r • 𝟙 d)).hom x) =
            (F.map (r • 𝟙 d')).hom ((F.map f).hom x)
          rw [← AddCommGrpCat.comp_apply, ← AddCommGrpCat.comp_apply, ← F.map_comp,
            ← F.map_comp, Linear.smul_comp, Linear.comp_smul, Category.id_comp,
            Category.comp_id] }

/-- **0.1** For an `R`-linear `C`, `Mod C` is `R`-linear through the derived actions. -/
instance : Linear R (ModCat.{w} D) := sorry

end Linear

/-! ### 0.2 Rings as one-object categories -/

section OneObject

variable (A : Type u) [Ring A]

/-- **0.2** Left `A`-modules are the additive functors on `SingleObj A` (Mathlib's
`f ≫ g = g * f`); the pattern of Mathlib's `Action.functorCategoryEquivalence`. -/
noncomputable def moduleCatEquivLeftModCat : ModuleCat.{v} A ≌ LeftModCat.{v} (SingleObj A) :=
  sorry

/-- **0.2** Right `A`-modules are the additive functors on `(SingleObj A)ᵒᵖ`. -/
noncomputable def moduleCatMulOppositeEquivModCat :
    ModuleCat.{v} Aᵐᵒᵖ ≌ ModCat.{v} (SingleObj A) :=
  sorry

/-- **0.2** The regular left module goes to the representable `Hom(∗, -)`. -/
noncomputable def moduleCatEquivLeftModCatRegularIso :
    (moduleCatEquivLeftModCat.{u} A).functor.obj (ModuleCat.of A A) ≅
      (LeftModCat.coyoneda (SingleObj A)).obj (op (SingleObj.star A)) :=
  sorry

/-- **0.2** The regular right module goes to the representable `Hom(-, ∗)`. -/
noncomputable def moduleCatMulOppositeEquivModCatRegularIso :
    (moduleCatMulOppositeEquivModCat.{u} A).functor.obj (ModuleCat.of Aᵐᵒᵖ A) ≅
      (ModCat.yoneda (SingleObj A)).obj (SingleObj.star A) :=
  sorry

/-- **0.2** `SingleObj Aᵐᵒᵖ` is the opposite of `SingleObj A`. -/
noncomputable def singleObjMulOppositeEquiv : SingleObj Aᵐᵒᵖ ≌ (SingleObj A)ᵒᵖ :=
  sorry

instance : (singleObjMulOppositeEquiv A).functor.Additive := sorry

/-- **0.2** `SingleObj A` is `w`-small when `A` is. -/
instance [Small.{v} A] : EssentiallySmall.{v} (SingleObj A) := sorry

/-- **0.2** For an `R`-algebra `A`, `SingleObj A` is `R`-linear. -/
instance (R : Type*) [CommRing R] [Algebra R A] : Linear R (SingleObj A) where
  homModule _ _ := inferInstanceAs (Module R A)
  smul_comp _ _ _ r f g := mul_smul_comm r g f
  comp_smul _ _ _ f r g := smul_mul_assoc r g f

/-- **0.2** The derived `R`-structure at `∗` is the `R`-structure through `algebraMap R A`. -/
noncomputable def moduleCatEquivLeftModCatToModuleCatIso (R : Type*) [CommRing R]
    [Algebra R A] (M : ModuleCat.{v} A) :
    (Functor.toModuleCat R ((moduleCatEquivLeftModCat.{v} A).functor.obj M).obj).obj
        (SingleObj.star A) ≅
      (ModuleCat.restrictScalars (algebraMap R A)).obj M :=
  sorry

end OneObject

/-! ### 0.3 The tensor product over `C` -/

section Tensor

variable (R : Type*) [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C]

/-- **0.3** The bifunctor `(c', c) ↦ F(c') ⊗_R G(c)`, whose coend is `F ⊗_C G`. -/
def tensorBifunctor (F : Cᵒᵖ ⥤ ModuleCat.{w} R) (G : C ⥤ ModuleCat.{w} R) :
    Cᵒᵖ ⥤ C ⥤ ModuleCat.{w} R where
  obj c' :=
    { obj c := ModuleCat.of R (F.obj c' ⊗[R] G.obj c)
      map g := ModuleCat.ofHom ((G.map g).hom.lTensor _)
      map_id c := by ext : 1; simp
      map_comp f g := by ext : 1; simp [LinearMap.lTensor_comp] }
  map f :=
    { app c := ModuleCat.ofHom ((F.map f).hom.rTensor _)
      naturality _ _ g := by
        ext : 1; simp [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor] }
  map_id c' := by ext : 2; simp
  map_comp f g := by ext : 2; simp [LinearMap.rTensor_comp]

/-- **0.3** The coend exists when `C` is `w`-small. -/
instance [EssentiallySmall.{w} C] (F : Cᵒᵖ ⥤ ModuleCat.{w} R) (G : C ⥤ ModuleCat.{w} R) :
    HasCoend (tensorBifunctor R F G) :=
  sorry

namespace ModCat

/-- **0.3** `Hom_R(G(-), X)` as a right `C`-module, functorial in `G` and `X`. -/
noncomputable def homRightBifunctor : (LeftModCat.{w} C)ᵒᵖ ⥤ ModuleCat.{w} R ⥤ ModCat.{w} C :=
  sorry

/-- **0.3** `Hom_R(F(-), X)` as a left `C`-module, functorial in `F` and `X`. -/
noncomputable def homLeftBifunctor : (ModCat.{w} C)ᵒᵖ ⥤ ModuleCat.{w} R ⥤ LeftModCat.{w} C :=
  sorry

/-- **0.3** `X ↦ Hom_R(G(-), X)`. -/
noncomputable abbrev homRight (G : LeftModCat.{w} C) : ModuleCat.{w} R ⥤ ModCat.{w} C :=
  (homRightBifunctor R).obj (op G)

/-- **0.3** `X ↦ Hom_R(F(-), X)`. -/
noncomputable abbrev homLeft (F : ModCat.{w} C) : ModuleCat.{w} R ⥤ LeftModCat.{w} C :=
  (homLeftBifunctor R).obj (op F)

variable [Linear R C] [EssentiallySmall.{w} C]

/-- **0.3** `F ⊗_C G`: the coend in `ModuleCat R` of `F(c) ⊗_R G(c)`, with the derived
`R`-structures (0.1). -/
noncomputable def tensorObj (F : ModCat.{w} C) (G : LeftModCat.{w} C) : ModuleCat.{w} R :=
  coend (tensorBifunctor R (Functor.toModuleCat R F.obj) (Functor.toModuleCat R G.obj))

variable {R}

/-- **0.3** The element `x ⊗ y` of `F ⊗_C G` for `x ∈ F(c)` and `y ∈ G(c)`. -/
noncomputable def tmul {F : ModCat.{w} C} {G : LeftModCat.{w} C} (c : C) (x : F.obj.obj (op c))
    (y : G.obj.obj c) : tensorObj R F G :=
  (coend.ι (tensorBifunctor R (Functor.toModuleCat R F.obj) (Functor.toModuleCat R G.obj)) c).hom
    (TensorProduct.tmul R (M := (Functor.toModuleCat R F.obj).obj (op c))
      (N := (Functor.toModuleCat R G.obj).obj c) x y)

/-- **0.3, balancing**: `x f ⊗ y = x ⊗ f y`. -/
theorem tmul_balance {F : ModCat.{w} C} {G : LeftModCat.{w} C} {c c' : C} (f : c ⟶ c')
    (x : F.obj.obj (op c')) (y : G.obj.obj c) :
    tmul (R := R) c ((F.obj.map f.op).hom x) y = tmul c' x ((G.obj.map f).hom y) :=
  sorry

/-- **0.3, induction** on `F ⊗_C G` by pure tensors and sums. -/
theorem tensorObj_induction_on {F : ModCat.{w} C} {G : LeftModCat.{w} C}
    {P : tensorObj R F G → Prop} (z : tensorObj R F G) (h₀ : P 0)
    (ht : ∀ (c : C) (x : F.obj.obj (op c)) (y : G.obj.obj c), P (tmul c x y))
    (ha : ∀ a b, P a → P b → P (a + b)) : P z :=
  sorry

/-- **0.3** Maps out of `F ⊗_C G` agree when they agree on pure tensors. -/
theorem tensorObj_hom_ext {F : ModCat.{w} C} {G : LeftModCat.{w} C} {X : ModuleCat.{w} R}
    {φ ψ : tensorObj R F G ⟶ X}
    (h : ∀ (c : C) (x : F.obj.obj (op c)) (y : G.obj.obj c),
      φ.hom (tmul c x y) = ψ.hom (tmul c x y)) : φ = ψ :=
  sorry

/-- **0.3** A balanced family of `R`-bilinear maps lifts to `F ⊗_C G`. -/
noncomputable def tensorLift {F : ModCat.{w} C} {G : LeftModCat.{w} C} {X : ModuleCat.{w} R}
    (φ : ∀ c : C, (Functor.toModuleCat R F.obj).obj (op c) →ₗ[R]
      (Functor.toModuleCat R G.obj).obj c →ₗ[R] X)
    (hφ : ∀ ⦃c c' : C⦄ (f : c ⟶ c') (x : F.obj.obj (op c')) (y : G.obj.obj c),
      φ c ((F.obj.map f.op).hom x) y = φ c' x ((G.obj.map f).hom y)) :
    tensorObj R F G ⟶ X :=
  sorry

theorem tensorLift_tmul {F : ModCat.{w} C} {G : LeftModCat.{w} C} {X : ModuleCat.{w} R}
    (φ : ∀ c : C, (Functor.toModuleCat R F.obj).obj (op c) →ₗ[R]
      (Functor.toModuleCat R G.obj).obj c →ₗ[R] X)
    (hφ : ∀ ⦃c c' : C⦄ (f : c ⟶ c') (x : F.obj.obj (op c')) (y : G.obj.obj c),
      φ c ((F.obj.map f.op).hom x) y = φ c' x ((G.obj.map f).hom y))
    (c : C) (x : F.obj.obj (op c)) (y : G.obj.obj c) :
    (tensorLift φ hφ).hom (tmul c x y) = φ c x y :=
  sorry

variable (R)

/-- **0.3** The tensor product as an `R`-linear bifunctor. -/
noncomputable def tensor : ModCat.{w} C ⥤ LeftModCat.{w} C ⥤ ModuleCat.{w} R where
  obj F :=
    { obj G := tensorObj R F G
      map _ := sorry
      map_id := sorry
      map_comp := sorry }
  map _ := { app _ := sorry, naturality := sorry }
  map_id := sorry
  map_comp := sorry

theorem tensor_map_app_tmul {F F' : ModCat.{w} C} (f : F ⟶ F') (G : LeftModCat.{w} C) (c : C)
    (x : F.obj.obj (op c)) (y : G.obj.obj c) :
    (((tensor R).map f).app G).hom (tmul c x y) = tmul c ((f.hom.app (op c)).hom x) y :=
  sorry

theorem tensor_obj_map_tmul (F : ModCat.{w} C) {G G' : LeftModCat.{w} C} (g : G ⟶ G') (c : C)
    (x : F.obj.obj (op c)) (y : G.obj.obj c) :
    (((tensor R).obj F).map g).hom (tmul c x y) = tmul c x ((g.hom.app c).hom y) :=
  sorry

instance (F : ModCat.{w} C) : ((tensor R).obj F).Additive := sorry

instance (G : LeftModCat.{w} C) : ((tensor R).flip.obj G).Additive := sorry

/-- **0.3, adjunction**: `Hom_R(F ⊗_C G, X) ≅ Hom_{Mod C}(F, Hom_R(G(-), X))`. -/
noncomputable def tensorAdjunction (G : LeftModCat.{w} C) :
    (tensor R).flip.obj G ⊣ homRight R G :=
  sorry

/-- **0.3, adjunction** in the left-module variable. -/
noncomputable def tensorAdjunction' (F : ModCat.{w} C) : (tensor R).obj F ⊣ homLeft R F :=
  sorry

/-- **0.3, right exactness**: `- ⊗_C G` preserves colimits, from the adjunction. -/
theorem preservesColimits_tensor_flip_obj (G : LeftModCat.{w} C) :
    PreservesColimitsOfSize.{w, w} ((tensor R).flip.obj G) :=
  (tensorAdjunction R G).leftAdjoint_preservesColimits

/-- **0.3, right exactness** in the left-module variable. -/
theorem preservesColimits_tensor_obj (F : ModCat.{w} C) :
    PreservesColimitsOfSize.{w, w} ((tensor R).obj F) :=
  (tensorAdjunction' R F).leftAdjoint_preservesColimits

/-- **0.3, Yoneda**: `Hom(-, X) ⊗_C G ≅ G(X)`. -/
noncomputable def tensorObjYonedaIso {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
    [EssentiallySmall.{v} C] (X : C) (G : LeftModCat.{v} C) :
    tensorObj R ((ModCat.yoneda C).obj X) G ≅ (Functor.toModuleCat R G.obj).obj X :=
  sorry

/-- **0.3, Yoneda**: `F ⊗_C Hom(X, -) ≅ F(X)`. -/
noncomputable def tensorObjCoyonedaIso {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
    [EssentiallySmall.{v} C] (F : ModCat.{v} C) (X : C) :
    tensorObj R F ((LeftModCat.coyoneda C).obj (op X)) ≅ (Functor.toModuleCat R F.obj).obj (op X) :=
  sorry

/-- **0.3, change of base** along `R → R'`, when the `R`-structure of `C` comes from the
`R'`-structure. -/
noncomputable def tensorObjRestrictScalarsIso {R' : Type*} [CommRing R'] [Algebra R R']
    [Linear R' C] (h : ∀ (X Y : C) (r : R) (f : X ⟶ Y), r • f = algebraMap R R' r • f)
    (F : ModCat.{w} C) (G : LeftModCat.{w} C) :
    (ModuleCat.restrictScalars (algebraMap R R')).obj (tensorObj R' F G) ≅ tensorObj R F G :=
  sorry

/-- **0.3, independence of `R`**: the underlying groups of the `R`-tensor and the `ℤ`-tensor
agree (`ℤ` acts through Mathlib's `preadditiveIntLinear`). -/
noncomputable def tensorObjIntIso (F : ModCat.{w} C) (G : LeftModCat.{w} C) :
    (ModuleCat.restrictScalars (algebraMap ℤ R)).obj (tensorObj R F G) ≅ tensorObj ℤ F G :=
  sorry

/-! ### 0.4 Projective factors -/

/-- **0.4** Tensoring with a projective right module preserves monomorphisms. -/
theorem mono_tensor_obj_map_of_projective (F : ModCat.{w} C) [Projective F]
    {G G' : LeftModCat.{w} C} (g : G ⟶ G') [Mono g] : Mono (((tensor R).obj F).map g) :=
  sorry

/-- **0.4** Tensoring with a projective left module preserves monomorphisms. -/
theorem mono_tensor_map_app_of_projective (G : LeftModCat.{w} C) [Projective G]
    {F F' : ModCat.{w} C} (f : F ⟶ F') [Mono f] : Mono (((tensor R).map f).app G) :=
  sorry

end ModCat

/-! ### 0.5 The swap -/

/-- **0.5** A left `C`-module as a right `Cᵒᵖ`-module, through `Cᵒᵖᵒᵖ ⥤ C`. -/
def LeftModCat.toModCatOp (C : Type u) [Category.{v} C] [Preadditive C] :
    LeftModCat.{w} C ⥤ ModCat.{w} Cᵒᵖ :=
  sorry

/-- **0.5, swap**: `F ⊗_C G ≅ G ⊗_{Cᵒᵖ} F`, with `F` a left `Cᵒᵖ`-module as it stands. -/
noncomputable def ModCat.tensorObjSwapIso [Linear R C] [EssentiallySmall.{w} C]
    (F : ModCat.{w} C) (G : LeftModCat.{w} C) :
    ModCat.tensorObj R F G ≅ ModCat.tensorObj R ((LeftModCat.toModCatOp C).obj G) F :=
  sorry

end Tensor

/-! ### 0.6 Rings: the balanced tensor product -/

namespace BalancedTensorProduct

section Maps

variable (R : Type t) [CommRing R] {A : Type u} [Ring A] [Algebra R A]
  {M M' M'' : Type*} [AddCommGroup M] [Module Aᵐᵒᵖ M] [Module R M] [IsScalarTower R Aᵐᵒᵖ M]
  [AddCommGroup M'] [Module Aᵐᵒᵖ M'] [Module R M'] [IsScalarTower R Aᵐᵒᵖ M']
  [AddCommGroup M''] [Module Aᵐᵒᵖ M''] [Module R M''] [IsScalarTower R Aᵐᵒᵖ M'']
  {N N' N'' : Type*} [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
  [AddCommGroup N'] [Module A N'] [Module R N'] [IsScalarTower R A N']
  [AddCommGroup N''] [Module A N''] [Module R N''] [IsScalarTower R A N'']

variable (N) in
/-- **0.6** `f ⊗ N : M ⊗_A N → M' ⊗_A N`, `R`-linear, named after Mathlib's
`LinearMap.rTensor`. -/
def rTensor (f : M →ₗ[Aᵐᵒᵖ] M') :
    TauCeti.BalancedTensorProduct R A M N →ₗ[R] TauCeti.BalancedTensorProduct R A M' N :=
  TauCeti.BalancedTensorProduct.map (f.restrictScalars R) LinearMap.id
    (fun a m ↦ f.map_smul (op a) m) (fun _ _ ↦ rfl)

variable (M) in
/-- **0.6** `M ⊗ g : M ⊗_A N → M ⊗_A N'`, `R`-linear, named after Mathlib's
`LinearMap.lTensor`. -/
def lTensor (g : N →ₗ[A] N') :
    TauCeti.BalancedTensorProduct R A M N →ₗ[R] TauCeti.BalancedTensorProduct R A M N' :=
  TauCeti.BalancedTensorProduct.map LinearMap.id (g.restrictScalars R)
    (fun _ _ ↦ rfl) (fun a n ↦ g.map_smul a n)

omit [IsScalarTower R A N] in
@[simp]
theorem rTensor_tmul (f : M →ₗ[Aᵐᵒᵖ] M') (m : M) (n : N) :
    rTensor R N f (TauCeti.BalancedTensorProduct.tmul R A m n) =
      TauCeti.BalancedTensorProduct.tmul R A (f m) n :=
  TauCeti.BalancedTensorProduct.map_tmul _ _ _ _ m n

omit [IsScalarTower R Aᵐᵒᵖ M] in
@[simp]
theorem lTensor_tmul (g : N →ₗ[A] N') (m : M) (n : N) :
    lTensor R M g (TauCeti.BalancedTensorProduct.tmul R A m n) =
      TauCeti.BalancedTensorProduct.tmul R A m (g n) :=
  TauCeti.BalancedTensorProduct.map_tmul _ _ _ _ m n

omit [IsScalarTower R A N] in
theorem rTensor_id : rTensor R N (LinearMap.id : M →ₗ[Aᵐᵒᵖ] M) = LinearMap.id :=
  TauCeti.BalancedTensorProduct.hom_ext fun _ _ ↦ by simp

omit [IsScalarTower R A N] in
theorem rTensor_comp (f : M →ₗ[Aᵐᵒᵖ] M') (f' : M' →ₗ[Aᵐᵒᵖ] M'') :
    rTensor R N (f' ∘ₗ f) = rTensor R N f' ∘ₗ rTensor R N f :=
  TauCeti.BalancedTensorProduct.hom_ext fun _ _ ↦ by simp

omit [IsScalarTower R Aᵐᵒᵖ M] in
theorem lTensor_id : lTensor R M (LinearMap.id : N →ₗ[A] N) = LinearMap.id :=
  TauCeti.BalancedTensorProduct.hom_ext fun _ _ ↦ by simp

omit [IsScalarTower R Aᵐᵒᵖ M] in
theorem lTensor_comp (g : N →ₗ[A] N') (g' : N' →ₗ[A] N'') :
    lTensor R M (g' ∘ₗ g) = lTensor R M g' ∘ₗ lTensor R M g :=
  TauCeti.BalancedTensorProduct.hom_ext fun _ _ ↦ by simp

theorem rTensor_comp_lTensor (f : M →ₗ[Aᵐᵒᵖ] M') (g : N →ₗ[A] N') :
    rTensor R N' f ∘ₗ lTensor R M g = lTensor R M' g ∘ₗ rTensor R N f :=
  TauCeti.BalancedTensorProduct.hom_ext fun _ _ ↦ by simp

/-- **0.6, right exactness** in the right-module variable. -/
theorem rTensor_exact {f : M →ₗ[Aᵐᵒᵖ] M'} {g : M' →ₗ[Aᵐᵒᵖ] M''} (hfg : Function.Exact f g)
    (hg : Function.Surjective g) : Function.Exact (rTensor R N f) (rTensor R N g) :=
  sorry

/-- **0.6** Tensoring preserves surjections in the right-module variable. -/
theorem rTensor_surjective {g : M' →ₗ[Aᵐᵒᵖ] M''} (hg : Function.Surjective g) :
    Function.Surjective (rTensor R N g) :=
  sorry

/-- **0.6, right exactness** in the left-module variable. -/
theorem lTensor_exact {f : N →ₗ[A] N'} {g : N' →ₗ[A] N''} (hfg : Function.Exact f g)
    (hg : Function.Surjective g) : Function.Exact (lTensor R M f) (lTensor R M g) :=
  sorry

/-- **0.6** Tensoring preserves surjections in the left-module variable. -/
theorem lTensor_surjective {g : N' →ₗ[A] N''} (hg : Function.Surjective g) :
    Function.Surjective (lTensor R M g) :=
  sorry

/-- **0.6** Tensoring with a projective right module preserves injections (0.4). -/
theorem lTensor_injective_of_projective [Module.Projective Aᵐᵒᵖ M] {g : N →ₗ[A] N'}
    (hg : Function.Injective g) : Function.Injective (lTensor R M g) :=
  sorry

/-- **0.6** Tensoring with a projective left module preserves injections (0.4). -/
theorem rTensor_injective_of_projective [Module.Projective A N] {f : M →ₗ[Aᵐᵒᵖ] M'}
    (hf : Function.Injective f) : Function.Injective (rTensor R N f) :=
  sorry

variable (M N) in
/-- **0.6, independence of `R`**: the `ℤ`- and `R`-balanced tensor products have the same
underlying group, `m ⊗ n ↦ m ⊗ n`. -/
noncomputable def intAddEquiv :
    TauCeti.BalancedTensorProduct ℤ A M N ≃+ TauCeti.BalancedTensorProduct R A M N :=
  sorry

variable (M N) in
/-- **0.6, change of base** along `R → R'` for `R'`-modules: `m ⊗ n ↦ m ⊗ n`, `R`-linear (stated
here on underlying groups). -/
noncomputable def changeBaseAddEquiv (R' : Type*) [CommRing R'] [Algebra R R'] [Algebra R' A]
    [IsScalarTower R R' A] [Module R' M] [IsScalarTower R' Aᵐᵒᵖ M] [IsScalarTower R R' M]
    [Module R' N] [IsScalarTower R' A N] [IsScalarTower R R' N] :
    TauCeti.BalancedTensorProduct R A M N ≃+ TauCeti.BalancedTensorProduct R' A M N :=
  sorry

variable (M N) in
/-- **0.6, swap**: `M ⊗_A N ≃ N ⊗_{Aᵐᵒᵖ} M`, `m ⊗ n ↦ n ⊗ m`, with `N` a right
`Aᵐᵒᵖ`-module through `RingEquiv.opOp A`. -/
noncomputable def comm :
    letI : Module Aᵐᵒᵖᵐᵒᵖ N := Module.compHom N (RingEquiv.opOp A).symm.toRingHom
    TauCeti.BalancedTensorProduct R A M N ≃ₗ[R] TauCeti.BalancedTensorProduct R Aᵐᵒᵖ N M :=
  sorry

variable (M N) in
/-- **0.6, duals** (0.7 for rings): `Hom_R(M ⊗_A N, E) ≃ Hom_{Aᵐᵒᵖ}(M, Hom_R(N, E))`, with
Tau Ceti's `MatlisDual R E N` as the right module `Hom_R(N, E)`. -/
noncomputable def homEquiv (E : Type*) [AddCommGroup E] [Module R E] :
    (TauCeti.BalancedTensorProduct R A M N →ₗ[R] E) ≃ₗ[R]
      (M →ₗ[Aᵐᵒᵖ] TauCeti.MatlisDual R E N) :=
  sorry

end Maps

section CharacterModule

variable {A : Type u} [Ring A]
  {M M' : Type*} [AddCommGroup M] [Module Aᵐᵒᵖ M] [AddCommGroup M'] [Module Aᵐᵒᵖ M']
  {N : Type*} [AddCommGroup N] [Module A N]

/-- **0.7 for rings, Lambek's criterion for one map** (`R = ℤ`, `E = ℚ ⧸ ℤ`): `f ⊗ N` is
injective exactly when composition with `f` is onto on maps into `N⁺`. -/
theorem rTensor_injective_iff_surjective_comp (f : M →ₗ[Aᵐᵒᵖ] M') :
    Function.Injective (rTensor ℤ N f) ↔
      Function.Surjective fun φ : M' →ₗ[Aᵐᵒᵖ] CharacterModule N ↦ φ ∘ₗ f :=
  sorry

end CharacterModule

/-- **0.6, commutative rings**: for a commutative ring, with `M` a right module through the same
action (`IsCentralScalar`), the balanced tensor product is Mathlib's tensor product. -/
noncomputable def equivTensorProduct {R : Type u} [CommRing R] (M N : Type*) [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] [AddCommGroup N] [Module R N] :
    TauCeti.BalancedTensorProduct R R M N ≃ₗ[R] M ⊗[R] N :=
  sorry

@[simp]
theorem equivTensorProduct_tmul {R : Type u} [CommRing R] {M N : Type*} [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] [AddCommGroup N] [Module R N] (m : M)
    (n : N) :
    equivTensorProduct M N (TauCeti.BalancedTensorProduct.tmul R R m n) = m ⊗ₜ[R] n :=
  sorry

section Functor

attribute [local instance] ModuleCat.moduleOfAlgebra ModuleCat.isScalarTower_moduleOfAlgebra

variable (R : Type t) [CommRing R] (A : Type u) [Ring A] [Algebra R A]

/-- **0.6** The balanced tensor product as a bifunctor
`ModuleCat Aᵐᵒᵖ ⥤ ModuleCat A ⥤ ModuleCat R`; the `R`-actions on bundled modules come from
Tau Ceti's `ModuleCat.moduleOfAlgebra`. -/
noncomputable def functor : ModuleCat.{v} Aᵐᵒᵖ ⥤ ModuleCat.{v} A ⥤ ModuleCat.{v} R where
  obj M :=
    { obj N := ModuleCat.of R (TauCeti.BalancedTensorProduct R A M N)
      map g := ModuleCat.ofHom (lTensor R M g.hom)
      map_id _ := ModuleCat.hom_ext (lTensor_id R)
      map_comp f g := ModuleCat.hom_ext (lTensor_comp R f.hom g.hom) }
  map f :=
    { app N := ModuleCat.ofHom (rTensor R N f.hom)
      naturality _ _ g := ModuleCat.hom_ext (rTensor_comp_lTensor R f.hom g.hom) }
  map_id _ := NatTrans.ext (funext fun _ ↦ ModuleCat.hom_ext (rTensor_id R))
  map_comp f g := NatTrans.ext (funext fun _ ↦ ModuleCat.hom_ext (rTensor_comp R f.hom g.hom))

/-- **0.6** The bifunctor is additive in the left-module variable. -/
instance (M : ModuleCat.{v} Aᵐᵒᵖ) : ((functor R A).obj M).Additive :=
  sorry

/-- **0.6** The bifunctor is additive in the right-module variable. -/
instance (N : ModuleCat.{v} A) : ((functor R A).flip.obj N).Additive :=
  sorry

/-- **0.6** `X ↦ Hom_R(N, X)` as a right `A`-module (Tau Ceti's `MatlisDual R X N`). -/
noncomputable def homRight (N : ModuleCat.{v} A) : ModuleCat.{v} R ⥤ ModuleCat.{v} Aᵐᵒᵖ where
  obj X := ModuleCat.of Aᵐᵒᵖ (TauCeti.MatlisDual R X N)
  map _ := sorry
  map_id := sorry
  map_comp := sorry

/-- **0.6, adjunction**: `- ⊗_A N ⊣ Hom_R(N, -)`; right exactness follows. -/
noncomputable def adjunction (N : ModuleCat.{v} A) : (functor R A).flip.obj N ⊣ homRight R A N :=
  sorry

/-- **0.6, comparison**: the categorical tensor product over `SingleObj A` (0.3) of the modules
of 0.2 is the balanced tensor product. -/
noncomputable def tensorObjSingleObjIso [Small.{v} A] (M : ModuleCat.{v} Aᵐᵒᵖ)
    (N : ModuleCat.{v} A) :
    ModCat.tensorObj R ((moduleCatMulOppositeEquivModCat.{v} A).functor.obj M)
        ((moduleCatEquivLeftModCat.{v} A).functor.obj N) ≅
      ((functor R A).obj M).obj N :=
  sorry

end Functor

end BalancedTensorProduct

/-! ### 0.7 Duals with respect to an `R`-module `E` -/

section Dual

variable (R : Type*) [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C]
  (E : ModuleCat.{w} R)

/-- **0.7** `G ↦ G^E = Hom_R(G(-), E)`, from left to right modules. -/
noncomputable abbrev LeftModCat.dual : (LeftModCat.{w} C)ᵒᵖ ⥤ ModCat.{w} C :=
  (ModCat.homRightBifunctor R).flip.obj E

/-- **0.7** `F ↦ F^E = Hom_R(F(-), E)`, from right to left modules. -/
noncomputable abbrev ModCat.dual : (ModCat.{w} C)ᵒᵖ ⥤ LeftModCat.{w} C :=
  (ModCat.homLeftBifunctor R).flip.obj E

instance : (LeftModCat.dual R E (C := C)).Additive := sorry

/-- **0.7** For an injective `E`, the dual is exact. -/
theorem LeftModCat.dual_shortExact [Injective E] {S : ShortComplex (LeftModCat.{w} C)}
    (hS : S.ShortExact) : (S.op.map (LeftModCat.dual R E)).ShortExact :=
  sorry

/-- **0.7** For a cogenerator `E`, the dual detects zero objects. -/
theorem LeftModCat.isZero_of_isZero_dual (hE : IsCoseparator E) (G : LeftModCat.{w} C)
    (h : IsZero ((LeftModCat.dual R E).obj (op G))) : IsZero G :=
  sorry

/-- **0.7, one-map form of Lambek's criterion**: for a cogenerator `E`, `i ⊗ G` is a
monomorphism exactly when composition with `i` is onto on maps into `G^E`. -/
theorem ModCat.mono_tensor_map_app_iff [Linear R C] [EssentiallySmall.{w} C]
    (hE : IsCoseparator E) {F F' : ModCat.{w} C} (i : F ⟶ F') (G : LeftModCat.{w} C) :
    Mono (((ModCat.tensor R).map i).app G) ↔
      Function.Surjective fun φ : F' ⟶ (LeftModCat.dual R E).obj (op G) ↦ i ≫ φ :=
  sorry

end Dual

/-! ## Layer 1: `Tor` over an arbitrary ring

Layers 1–4 are under review: they are to be converted to the category-primary design of Layer 0
and are currently stated for rings. `Tor` takes values in `ModuleCat R` for an `R`-algebra `A`;
Layers 2 and 3 use `R = ℤ` (by 0.3 the choice of `R` does not change the underlying groups). -/

/-- **1.1** `Small.{v} Aᵐᵒᵖ` from `Small.{v} A`, so that right modules have projective
resolutions in `ModuleCat.{v} Aᵐᵒᵖ`. -/
instance small_mulOpposite (A : Type u) [Small.{v} A] : Small.{v} Aᵐᵒᵖ :=
  small_of_injective MulOpposite.unop_injective

section Tor

variable (R : Type t) [CommRing R] (A : Type u) [Ring A] [Algebra R A] [Small.{v} A]

/-- **1.1** `Tor_n^A(M, N)`, derived in the left-module variable `N`, the shape of Mathlib's
`CategoryTheory.Tor`. -/
noncomputable def BalancedTor (n : ℕ) :
    ModuleCat.{v} Aᵐᵒᵖ ⥤ ModuleCat.{v} A ⥤ ModuleCat.{v} R where
  obj M := ((BalancedTensorProduct.functor R A).obj M).leftDerived n
  map f := NatTrans.leftDerived ((BalancedTensorProduct.functor R A).map f) n

/-- **1.1** `Tor_n^A(M, N)`, derived in the right-module variable `M`, the shape of Mathlib's
`CategoryTheory.Tor'`. -/
noncomputable def BalancedTor' (n : ℕ) :
    ModuleCat.{v} Aᵐᵒᵖ ⥤ ModuleCat.{v} A ⥤ ModuleCat.{v} R :=
  Functor.flip
    { obj N := ((BalancedTensorProduct.functor R A).flip.obj N).leftDerived n
      map g := NatTrans.leftDerived ((BalancedTensorProduct.functor R A).flip.map g) n }

/-- **1.1** `Tor_0` is the tensor product. -/
noncomputable def balancedTorZeroIso :
    BalancedTor.{v} R A 0 ≅ BalancedTensorProduct.functor.{v} R A :=
  sorry

/-- **1.1** `Tor'_0` is the tensor product. -/
noncomputable def balancedTor'ZeroIso :
    BalancedTor'.{v} R A 0 ≅ BalancedTensorProduct.functor.{v} R A :=
  sorry

variable {R A}

/-- **1.1** Higher `Tor` vanishes at a projective left module. -/
theorem isZero_balancedTor_succ_of_projective (M : ModuleCat.{v} Aᵐᵒᵖ) (N : ModuleCat.{v} A)
    [Projective N] (n : ℕ) : IsZero (((BalancedTor R A (n + 1)).obj M).obj N) :=
  sorry

/-- **1.1** Higher `Tor'` vanishes at a projective right module. -/
theorem isZero_balancedTor'_succ_of_projective (M : ModuleCat.{v} Aᵐᵒᵖ) [Projective M]
    (N : ModuleCat.{v} A) (n : ℕ) : IsZero (((BalancedTor' R A (n + 1)).obj M).obj N) :=
  sorry

section LongExact

variable {S : ShortComplex (ModuleCat.{v} Aᵐᵒᵖ)}

/-- **1.2** The connecting map `Tor_{n+1}(M₃, N) → Tor_n(M₁, N)` of a short exact sequence of
right modules. -/
noncomputable def ShortComplex.ShortExact.balancedTorδ (hS : S.ShortExact) (N : ModuleCat.{v} A)
    (n : ℕ) :
    ((BalancedTor R A (n + 1)).obj S.X₃).obj N ⟶ ((BalancedTor R A n).obj S.X₁).obj N :=
  sorry

/-- **1.2** Exactness at `Tor_n(M₁, N)`. -/
theorem balancedTor_exact₁ (hS : S.ShortExact) (N : ModuleCat.{v} A) (n : ℕ) :
    Function.Exact (ShortComplex.ShortExact.balancedTorδ hS N n).hom
      (((BalancedTor R A n).map S.f).app N).hom :=
  sorry

/-- **1.2** Exactness at `Tor_n(M₂, N)`. -/
theorem balancedTor_exact₂ (hS : S.ShortExact) (N : ModuleCat.{v} A) (n : ℕ) :
    Function.Exact (((BalancedTor R A n).map S.f).app N).hom
      (((BalancedTor R A n).map S.g).app N).hom :=
  sorry

/-- **1.2** Exactness at `Tor_{n+1}(M₃, N)`. -/
theorem balancedTor_exact₃ (hS : S.ShortExact) (N : ModuleCat.{v} A) (n : ℕ) :
    Function.Exact (((BalancedTor R A (n + 1)).map S.g).app N).hom
      (ShortComplex.ShortExact.balancedTorδ hS N n).hom :=
  sorry

end LongExact

variable (R A) in
/-- **1.3, balance**: the two derivations of `Tor` agree. -/
noncomputable def balancedTorIso (n : ℕ) : BalancedTor.{v} R A n ≅ BalancedTor'.{v} R A n :=
  sorry

/-- **1.4, commutative rings**: over a commutative ring, `BalancedTor R R` is Mathlib's
`CategoryTheory.Tor`. -/
noncomputable def balancedTorIsoTor (R : Type u) [CommRing R] (n : ℕ) :
    ModuleCat.restrictScalars.{u} (RingEquiv.toOpposite R).symm.toRingHom ⋙ BalancedTor.{u} R R n ≅
      Tor (ModuleCat.{u} R) n :=
  sorry

/-- **1.4, cyclic modules**: for a right ideal `I` and a left ideal `K`,
`Tor_1^A(A ⧸ I, A ⧸ K) ≃+ (I ∩ K) ⧸ IK`, with `IK` the additive subgroup generated by products. -/
noncomputable def balancedTorOneQuotientEquiv (A : Type u) [Ring A] (I : Submodule Aᵐᵒᵖ A)
    (K : Ideal A) :
    (((BalancedTor.{u} ℤ A 1).obj (ModuleCat.of Aᵐᵒᵖ (A ⧸ I))).obj (ModuleCat.of A (A ⧸ K))) ≃+
      ↥(I.toAddSubgroup ⊓ K.toAddSubgroup) ⧸
        (AddSubgroup.closure (Set.image2 (· * ·) (I : Set A) (K : Set A))).addSubgroupOf
          (I.toAddSubgroup ⊓ K.toAddSubgroup) :=
  sorry

end Tor

/-! ## Layer 2: flat modules -/

/-- **2.1** A left module `M` is flat when `N ⊗_A M → P ⊗_A M` is injective for every finite right
module `P` in the universe of `A` and every finitely generated submodule `N ≤ P`: the shape of
Mathlib's `Module.Flat`. A right module `M` is flat when `Module.BalancedFlat Aᵐᵒᵖ M`. -/
class Module.BalancedFlat (A : Type u) (M : Type v) [Ring A] [AddCommGroup M] [Module A M] :
    Prop where
  out ⦃P : Type u⦄ [AddCommGroup P] [Module Aᵐᵒᵖ P] [Module.Finite Aᵐᵒᵖ P]
    (N : Submodule Aᵐᵒᵖ P) : N.FG →
      Function.Injective (BalancedTensorProduct.rTensor ℤ M N.subtype)

section Flat

variable {A : Type u} [Ring A]

/-- **2.1, tests for flatness**: the definition; all injections of right modules; finitely
generated right ideals; Lambek's character-module test; vanishing of `Tor_1`; vanishing of `Tor_1`
on cyclic right modules. -/
theorem Module.balancedFlat_tfae [Small.{v} A] (M : Type v) [AddCommGroup M] [Module A M] :
    List.TFAE
      [Module.BalancedFlat A M,
        ∀ ⦃P Q : Type v⦄ [AddCommGroup P] [Module Aᵐᵒᵖ P] [AddCommGroup Q] [Module Aᵐᵒᵖ Q]
          (i : P →ₗ[Aᵐᵒᵖ] Q), Function.Injective i →
            Function.Injective (BalancedTensorProduct.rTensor ℤ M i),
        ∀ I : Submodule Aᵐᵒᵖ A, I.FG →
          Function.Injective (BalancedTensorProduct.rTensor ℤ M I.subtype),
        Module.Injective Aᵐᵒᵖ (CharacterModule M),
        ∀ N : ModuleCat.{v} Aᵐᵒᵖ,
          IsZero (((BalancedTor.{v} ℤ A 1).obj N).obj (ModuleCat.of A M)),
        ∀ I : Submodule Aᵐᵒᵖ A, I.FG →
          IsZero (((BalancedTor.{v} ℤ A 1).obj (ModuleCat.of Aᵐᵒᵖ (Shrink.{v} (A ⧸ I)))).obj
            (ModuleCat.of A M))] :=
  sorry

/-- **2.1, commutative rings**: over a commutative ring, `BalancedFlat` is Mathlib's
`Module.Flat`. -/
theorem Module.balancedFlat_iff_flat {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M]
    [Module R M] : Module.BalancedFlat R M ↔ Module.Flat R M :=
  sorry

variable {M M₁ M₂ M₃ : Type v} [AddCommGroup M] [Module A M] [AddCommGroup M₁] [Module A M₁]
  [AddCommGroup M₂] [Module A M₂] [AddCommGroup M₃] [Module A M₃]

/-- **2.2** Projective modules are flat (an instance in Tau Ceti). -/
theorem Module.BalancedFlat.of_projective [Module.Projective A M] : Module.BalancedFlat A M :=
  sorry

/-- **2.2** Flatness is invariant under linear equivalence. -/
theorem Module.BalancedFlat.of_linearEquiv (e : M₁ ≃ₗ[A] M₂) [Module.BalancedFlat A M₁] :
    Module.BalancedFlat A M₂ :=
  sorry

/-- **2.2** A direct sum is flat exactly when every summand is. -/
theorem Module.balancedFlat_directSum_iff {ι : Type v} (N : ι → Type v)
    [∀ i, AddCommGroup (N i)] [∀ i, Module A (N i)] :
    Module.BalancedFlat A (⨁ i, N i) ↔ ∀ i, Module.BalancedFlat A (N i) :=
  sorry

/-- **2.2** In a short exact sequence with flat third term, the middle term is flat exactly when
the first is. -/
theorem Module.balancedFlat_iff_of_exact [Small.{v} A] {f : M₁ →ₗ[A] M₂} {g : M₂ →ₗ[A] M₃}
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    [Module.BalancedFlat A M₃] : Module.BalancedFlat A M₂ ↔ Module.BalancedFlat A M₁ :=
  sorry

/-- **2.2** Flat modules have no higher `Tor`. -/
theorem isZero_balancedTor_succ_of_balancedFlat [Small.{v} A] (N : ModuleCat.{v} Aᵐᵒᵖ)
    (M : ModuleCat.{v} A) [Module.BalancedFlat A M] (n : ℕ) :
    IsZero (((BalancedTor ℤ A (n + 1)).obj N).obj M) :=
  sorry

/-- **2.3, flat quotients**: if `F` and `F ⧸ K` are flat, then `K ∩ IF = IK` for every two-sided
ideal `I`. -/
theorem Submodule.inf_smul_eq_smul_of_balancedFlat {F : Type v} [AddCommGroup F] [Module A F]
    [Module.BalancedFlat A F] (K : Submodule A F) [Module.BalancedFlat A (F ⧸ K)] (I : Ideal A)
    [I.IsTwoSided] : K ⊓ I • (⊤ : Submodule A F) = I • K :=
  sorry

variable (A) in
/-- **2.3** The relations of Bass's flat module: the span of the `eᵢ - aᵢ • eᵢ₊₁` in `ℕ →₀ A`. -/
noncomputable def bassRelations (a : ℕ → A) : Submodule A (ℕ →₀ A) :=
  Submodule.span A (Set.range fun i ↦ Finsupp.single i 1 - Finsupp.single (i + 1) (a i))

/-- **2.3, Bass's flat module** is flat. -/
theorem balancedFlat_bassRelations (a : ℕ → A) :
    Module.BalancedFlat A ((ℕ →₀ A) ⧸ bassRelations A a) :=
  sorry

/-- **2.3** If Bass's module is projective, the chain of principal right ideals
`a₀A ⊇ a₀a₁A ⊇ a₀a₁a₂A ⊇ ⋯` is eventually constant. -/
theorem exists_span_prod_eq_of_projective_bassRelations (a : ℕ → A)
    [Module.Projective A ((ℕ →₀ A) ⧸ bassRelations A a)] :
    ∃ n, ∀ m ≥ n, Submodule.span Aᵐᵒᵖ {(List.ofFn fun i : Fin m ↦ a i).prod} =
      Submodule.span Aᵐᵒᵖ {(List.ofFn fun i : Fin n ↦ a i).prod} :=
  sorry

/-- **2.4** A finitely presented flat module is projective. -/
theorem Module.BalancedFlat.projective_of_finitePresentation [Small.{v} A]
    [Module.FinitePresentation A M] [Module.BalancedFlat A M] : Module.Projective A M :=
  sorry

end Flat

/-! ## Layer 3: flat dimension and weak global dimension -/

section Dimension

variable {A : Type u} [Ring A] [Small.{v} A]

/-- **3.1** `M` has flat dimension `< n`: `Tor_i^A(N, M) = 0` for every right module `N` and every
`i ≥ n`. The shape of Mathlib's `HasProjectiveDimensionLT`. -/
class HasFlatDimensionLT (M : ModuleCat.{v} A) (n : ℕ) : Prop where
  isZero (i : ℕ) (hi : n ≤ i) (N : ModuleCat.{v} Aᵐᵒᵖ) :
    IsZero (((BalancedTor.{v} ℤ A i).obj N).obj M)

/-- **3.1** `M` has flat dimension `≤ n`. -/
abbrev HasFlatDimensionLE (M : ModuleCat.{v} A) (n : ℕ) : Prop :=
  HasFlatDimensionLT M (n + 1)

/-- **3.1** The flat dimension, in `WithBot ℕ∞`, `⊥` exactly for the zero module. The shape of
Mathlib's `projectiveDimension`. -/
noncomputable def flatDimension (M : ModuleCat.{v} A) : WithBot ℕ∞ :=
  sInf {d : WithBot ℕ∞ | ∀ i : ℕ, d < i → HasFlatDimensionLT M i}

theorem flatDimension_eq_bot_iff (M : ModuleCat.{v} A) : flatDimension M = ⊥ ↔ IsZero M :=
  sorry

/-- **3.1** Flat dimension `≤ 0` is flatness. -/
theorem hasFlatDimensionLE_zero_iff (M : ModuleCat.{v} A) :
    HasFlatDimensionLE M 0 ↔ Module.BalancedFlat A M :=
  sorry

theorem flatDimension_le_projectiveDimension (M : ModuleCat.{v} A) :
    flatDimension M ≤ projectiveDimension M :=
  sorry

/-- **3.1, dimension shifting** along `0 → K → F → M → 0` with `F` flat. -/
theorem hasFlatDimensionLE_succ_iff {S : ShortComplex (ModuleCat.{v} A)} (hS : S.ShortExact)
    [Module.BalancedFlat A S.X₂] (n : ℕ) :
    HasFlatDimensionLE S.X₃ (n + 1) ↔ HasFlatDimensionLE S.X₁ n :=
  sorry

/-- **3.1, the ideal test** for flat dimension. -/
theorem hasFlatDimensionLE_iff_forall_quotient (M : ModuleCat.{v} A) (n : ℕ) :
    HasFlatDimensionLE M n ↔ ∀ I : Submodule Aᵐᵒᵖ A, I.FG →
      IsZero (((BalancedTor.{v} ℤ A (n + 1)).obj (ModuleCat.of Aᵐᵒᵖ (Shrink.{v} (A ⧸ I)))).obj
        M) :=
  sorry

/-- **3.1** The flat dimension of `M` is the injective dimension of its character module. -/
theorem flatDimension_eq_injectiveDimension_characterModule (M : ModuleCat.{v} A) :
    flatDimension M = injectiveDimension (ModuleCat.of Aᵐᵒᵖ (CharacterModule M)) :=
  sorry

variable (A) in
/-- **3.2** The weak global dimension. -/
noncomputable def weakGlobalDimension : WithBot ℕ∞ :=
  ⨆ M : ModuleCat.{v} A, flatDimension M

theorem weakGlobalDimension_le_iff (n : ℕ) :
    weakGlobalDimension.{v} A ≤ n ↔
      ∀ (N : ModuleCat.{v} Aᵐᵒᵖ) (M : ModuleCat.{v} A),
        IsZero (((BalancedTor.{v} ℤ A (n + 1)).obj N).obj M) :=
  sorry

variable (A) in
/-- **3.2, symmetry**: the weak global dimension is left-right symmetric. -/
theorem weakGlobalDimension_mulOpposite :
    weakGlobalDimension.{v} Aᵐᵒᵖ = weakGlobalDimension.{v} A :=
  sorry

variable (A) in
/-- **3.2, bounds** by the left global dimension. -/
theorem weakGlobalDimension_le_globalDimension :
    weakGlobalDimension.{v} A ≤ TauCeti.globalDimension.{v} A :=
  sorry

variable (A) in
/-- **3.2, bounds** by the right global dimension. -/
theorem weakGlobalDimension_le_globalDimension_mulOpposite :
    weakGlobalDimension.{v} A ≤ TauCeti.globalDimension.{v} Aᵐᵒᵖ :=
  sorry

/-- **3.2, tests** for the weak global dimension: finitely presented right modules, and cyclic
right modules with finitely generated relations. -/
theorem weakGlobalDimension_le_tfae (n : ℕ) :
    List.TFAE
      [weakGlobalDimension.{v} A ≤ n,
        ∀ N : ModuleCat.{v} Aᵐᵒᵖ, Module.FinitePresentation Aᵐᵒᵖ N → flatDimension N ≤ n,
        ∀ I : Submodule Aᵐᵒᵖ A, I.FG →
          flatDimension (ModuleCat.of Aᵐᵒᵖ (Shrink.{v} (A ⧸ I))) ≤ n] :=
  sorry

/-- **3.2, from projective dimension**. -/
theorem weakGlobalDimension_le_of_forall_finitePresentation (n : ℕ)
    (h : ∀ N : ModuleCat.{v} Aᵐᵒᵖ, Module.FinitePresentation Aᵐᵒᵖ N →
      HasProjectiveDimensionLE N n) :
    weakGlobalDimension.{v} A ≤ n :=
  sorry

variable (A) in
theorem weakGlobalDimension_eq_bot_iff : weakGlobalDimension.{v} A = ⊥ ↔ Subsingleton A :=
  sorry

variable (A) in
theorem weakGlobalDimension_eq_zero_of_isSemisimpleRing [IsSemisimpleRing A] [Nontrivial A] :
    weakGlobalDimension.{v} A = 0 :=
  sorry

/-- **3.3** Over a left Noetherian ring, a finite module has equal flat and projective
dimension. -/
theorem flatDimension_eq_projectiveDimension_of_finite [IsNoetherianRing A] (M : ModuleCat.{v} A)
    [Module.Finite A M] : flatDimension M = projectiveDimension M :=
  sorry

variable (A) in
/-- **3.3, Auslander's theorem**: a left Noetherian ring has equal left global and weak global
dimension. -/
theorem globalDimension_eq_weakGlobalDimension [IsNoetherianRing A] :
    TauCeti.globalDimension.{v} A = weakGlobalDimension.{v} A :=
  sorry

/-- **3.3, left bound**: over a left Noetherian ring, a bound on the projective dimension of the
finitely presented right modules bounds the left global dimension. -/
theorem globalDimension_le_of_forall_finitePresentation_mulOpposite [IsNoetherianRing A] (n : ℕ)
    (h : ∀ N : ModuleCat.{v} Aᵐᵒᵖ, Module.FinitePresentation Aᵐᵒᵖ N →
      HasProjectiveDimensionLE N n) :
    TauCeti.globalDimension.{v} A ≤ n :=
  sorry

end Dimension

/-! ## Layer 4: semiperfect and perfect rings, and Bass's Theorem P -/

section TNilpotent

variable {A : Type u} [Ring A]

/-- **4.1** A subset `S` is **left T-nilpotent** if for every sequence `a₀, a₁, …` in `S` some
product `a₀ a₁ ⋯ aₙ₋₁` vanishes. -/
def IsLeftTNilpotent (S : Set A) : Prop :=
  ∀ a : ℕ → A, (∀ i, a i ∈ S) → ∃ n, (List.ofFn fun i : Fin n ↦ a i).prod = 0

theorem IsLeftTNilpotent.mono {S T : Set A} (hT : IsLeftTNilpotent T) (h : S ⊆ T) :
    IsLeftTNilpotent S :=
  sorry

theorem isLeftTNilpotent_of_isNilpotent {I : Ideal A} (hI : IsNilpotent I) :
    IsLeftTNilpotent (I : Set A) :=
  sorry

theorem IsLeftTNilpotent.isNilpotent {S : Set A} (hS : IsLeftTNilpotent S) {x : A} (hx : x ∈ S) :
    IsNilpotent x :=
  sorry

theorem IsLeftTNilpotent.image {B : Type*} [Ring B] {S : Set A} (hS : IsLeftTNilpotent S)
    (f : A →+* B) : IsLeftTNilpotent (f '' S) :=
  sorry

/-- **4.1, Nakayama's lemma for all modules**. -/
theorem isLeftTNilpotent_tfae (J : Ideal A) :
    List.TFAE
      [IsLeftTNilpotent (J : Set A),
        ∀ (M : Type u) [AddCommGroup M] [Module A M], J • (⊤ : Submodule A M) = ⊤ → Subsingleton M,
        ∀ (M : Type u) [AddCommGroup M] [Module A M],
          TauCeti.IsSuperfluous (J • (⊤ : Submodule A M)),
        TauCeti.IsSuperfluous (J • (⊤ : Submodule A (ℕ →₀ A)))] :=
  sorry

/-- **4.1** For a left T-nilpotent left ideal, `J • M` is superfluous in every module, in every
universe. -/
theorem IsLeftTNilpotent.isSuperfluous_smul_top {J : Ideal A} (hJ : IsLeftTNilpotent (J : Set A))
    (M : Type w) [AddCommGroup M] [Module A M] : TauCeti.IsSuperfluous (J • (⊤ : Submodule A M)) :=
  sorry

end TNilpotent

section Semiperfect

/-! ### 4.2 Projective covers over semiperfect rings -/

variable {R : Type u} [Ring R]

/-- **4.2** A projective cover of a projective module is an isomorphism. -/
theorem IsProjectiveCover.bijective_of_projective {M P : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P] [Module.Projective R M] {f : P →ₗ[R] M}
    (hf : TauCeti.IsProjectiveCover f) : Function.Bijective f :=
  sorry

/-- **4.2** A surjection from a projective module with local endomorphism ring onto a nonzero
module is a projective cover. -/
theorem isProjectiveCover_of_isLocalRing_end {P S : Type*} [AddCommGroup P] [Module R P]
    [Module.Projective R P] [IsLocalRing (Module.End R P)] [AddCommGroup S] [Module R S]
    [Nontrivial S] {f : P →ₗ[R] S} (hf : Function.Surjective f) : TauCeti.IsProjectiveCover f :=
  sorry

/-- **4.2** The cover of a simple module has a local endomorphism ring. -/
theorem IsProjectiveCover.isLocalRing_end {P S : Type*} [AddCommGroup P] [Module R P]
    [AddCommGroup S] [Module R S] [IsSimpleModule R S] {p : P →ₗ[R] S}
    (hp : TauCeti.IsProjectiveCover p) : IsLocalRing (Module.End R P) :=
  sorry

/-- **4.2** If `M` has a projective cover, every surjection onto `M` from a projective module
restricts to a projective cover on a submodule of its source. This moves covers between
universes. -/
theorem IsProjectiveCover.exists_isProjectiveCover_comp_subtype {M P Q : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [Module.Projective R Q] {f : P →ₗ[R] M} (hf : TauCeti.IsProjectiveCover f) {g : Q →ₗ[R] M}
    (hg : Function.Surjective g) :
    ∃ Q₀ : Submodule R Q, TauCeti.IsProjectiveCover (g ∘ₗ Q₀.subtype) :=
  sorry

/-- **4.2** For a projective module `P`, `rad P = J • P`. -/
theorem jacobson_eq_jacobson_smul_top_of_projective (P : Type v) [AddCommGroup P] [Module R P]
    [Module.Projective R P] : Module.jacobson R P = Ring.jacobson R • (⊤ : Submodule R P) :=
  sorry

/-- **4.2** A nonzero projective module has a proper radical. -/
theorem jacobson_ne_top_of_projective (P : Type v) [AddCommGroup P] [Module R P]
    [Module.Projective R P] [Nontrivial P] : Module.jacobson R P ≠ ⊤ :=
  sorry

/-- **4.2, covers from covers of simple quotients**: if every simple quotient of a finitely
generated module `M` has a projective cover, then `M` has one whose source is a finite product of
covers `pᵢ : Pᵢ → M ⧸ Nᵢ` of simple quotients, the `i`-th component lifting `pᵢ`. -/
theorem exists_isProjectiveCover_pi_of_forall_isCoatom_exists_isProjectiveCover {M : Type v}
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (h : ∀ N : Submodule R M, IsCoatom N → ∃ (P : Type w) (_ : AddCommGroup P) (_ : Module R P)
      (p : P →ₗ[R] M ⧸ N), TauCeti.IsProjectiveCover p) :
    ∃ (n : ℕ) (P : Fin n → Type w) (_ : ∀ i, AddCommGroup (P i)) (_ : ∀ i, Module R (P i))
      (N : Fin n → Submodule R M) (p : ∀ i, P i →ₗ[R] M ⧸ N i) (f : (∀ i, P i) →ₗ[R] M),
      (∀ i, IsCoatom (N i)) ∧ (∀ i, TauCeti.IsProjectiveCover (p i)) ∧
        (∀ i, (N i).mkQ ∘ₗ f ∘ₗ LinearMap.single R P i = p i) ∧ TauCeti.IsProjectiveCover f :=
  sorry

/-- **4.2, covers over a semiperfect ring**: every finitely generated module has a projective
cover. -/
theorem exists_isProjectiveCover_of_isSemiperfectRing [TauCeti.IsSemiperfectRing R] (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module R P) (p : P →ₗ[R] M),
      TauCeti.IsProjectiveCover p :=
  sorry

/-- **4.2** A ring that is, as a left module over itself, a finite product of modules with local
endomorphism rings is semiperfect. -/
theorem IsSemiperfectRing.of_linearEquiv_pi {n : ℕ} {P : Fin n → Type*}
    [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)] [∀ i, IsLocalRing (Module.End R (P i))]
    (φ : R ≃ₗ[R] ∀ i, P i) : TauCeti.IsSemiperfectRing R :=
  sorry

variable (R) in
/-- **4.2, semiperfect rings by projective covers** (Sandomierski; Krause, Proposition 4.1). -/
theorem isSemiperfectRing_tfae :
    List.TFAE
      [TauCeti.IsSemiperfectRing R,
        ∃ (n : ℕ) (P : Fin n → Type u) (_ : ∀ i, AddCommGroup (P i)) (_ : ∀ i, Module R (P i)),
          (∀ i, Module.Projective R (P i)) ∧ (∀ i, IsLocalRing (Module.End R (P i))) ∧
            Nonempty (R ≃ₗ[R] ∀ i, P i),
        ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M], ∃ (P : Type u)
          (_ : AddCommGroup P) (_ : Module R P) (p : P →ₗ[R] M), TauCeti.IsProjectiveCover p,
        ∀ (S : Type u) [AddCommGroup S] [Module R S] [IsSimpleModule R S], ∃ (P : Type u)
          (_ : AddCommGroup P) (_ : Module R P) (p : P →ₗ[R] S), TauCeti.IsProjectiveCover p] :=
  sorry

/-- **4.2, minimal presentations**: a finitely presented module over a semiperfect ring has a
finite minimal projective presentation. This generalizes and replaces the semiprimary Noetherian
`TauCeti.FiniteProjectivePresentation.exists_isMinimal`. -/
theorem FiniteProjectivePresentation.exists_isMinimal [TauCeti.IsSemiperfectRing R]
    [Small.{v} R] {M : ModuleCat.{v} R} [Module.FinitePresentation R M] :
    ∃ P : TauCeti.FiniteProjectivePresentation M,
      TauCeti.IsMinimalProjectivePresentation P.p P.π :=
  sorry

end Semiperfect

section Perfect

/-! ### 4.3 Left perfect rings -/

/-- **4.3** A ring is **left perfect** if `A ⧸ J` is semisimple and `J` is left T-nilpotent.
Right perfect is `IsLeftPerfectRing Aᵐᵒᵖ`. -/
class IsLeftPerfectRing (A : Type u) [Ring A] : Prop where
  isSemisimpleRing : IsSemisimpleRing (A ⧸ Ring.jacobson A)
  isLeftTNilpotent : IsLeftTNilpotent (Ring.jacobson A : Set A)

variable {A : Type u} [Ring A]

/-- **4.3** A semiprimary ring is left perfect (an instance in Tau Ceti). -/
theorem IsLeftPerfectRing.of_isSemiprimaryRing [IsSemiprimaryRing A] : IsLeftPerfectRing A :=
  sorry

/-- **4.3** A left perfect ring is semiperfect (an instance in Tau Ceti). -/
theorem IsLeftPerfectRing.isSemiperfectRing [IsLeftPerfectRing A] : TauCeti.IsSemiperfectRing A :=
  sorry

/-- **4.3** Quotients, and more generally surjective images, of left perfect rings are left
perfect. -/
theorem IsLeftPerfectRing.of_surjective {B : Type*} [Ring B] [IsLeftPerfectRing A] (f : A →+* B)
    (hf : Function.Surjective f) : IsLeftPerfectRing B :=
  sorry

/-- **4.4** Over a left perfect ring every module, in every universe, has a projective cover, in
the form of Tau Ceti's `TauCeti.exists_isProjectiveCover`, which it generalizes from semiprimary
rings. -/
theorem IsLeftPerfectRing.exists_isProjectiveCover [IsLeftPerfectRing A] (M : Type v)
    [AddCommGroup M] [Module A M] :
    ∃ P : Submodule A (M →₀ A),
      TauCeti.IsProjectiveCover (Finsupp.linearCombination A id ∘ₗ P.subtype) :=
  sorry

/-- **4.5, auxiliary**: a ring with zero Jacobson radical and the descending chain condition on
principal right ideals is semisimple. -/
theorem isSemisimpleRing_of_wellFoundedLT_isPrincipal (hJ : Ring.jacobson A = ⊥)
    [WellFoundedLT {I : Submodule Aᵐᵒᵖ A // I.IsPrincipal}] : IsSemisimpleRing A :=
  sorry

variable (A) in
/-- **4.5, Bass's Theorem P.** -/
theorem isLeftPerfectRing_tfae :
    List.TFAE
      [IsLeftPerfectRing A,
        ∀ (M : Type u) [AddCommGroup M] [Module A M], ∃ (P : Type u) (_ : AddCommGroup P)
          (_ : Module A P) (p : P →ₗ[A] M), TauCeti.IsProjectiveCover p,
        ∀ (M : Type u) [AddCommGroup M] [Module A M], Module.BalancedFlat A M →
          Module.Projective A M,
        WellFoundedLT {I : Submodule Aᵐᵒᵖ A // I.IsPrincipal},
        ∀ M : ModuleCat.{u} A, flatDimension M = projectiveDimension M] :=
  sorry

variable (A) in
/-- **4.6** A left perfect ring has equal left global and weak global dimension. -/
theorem globalDimension_eq_weakGlobalDimension_of_isLeftPerfectRing [Small.{v} A]
    [IsLeftPerfectRing A] : TauCeti.globalDimension.{v} A = weakGlobalDimension.{v} A :=
  sorry

variable (A) in
/-- **4.6** A ring that is left and right perfect has equal left and right global dimension. -/
theorem globalDimension_mulOpposite_of_isLeftPerfectRing [Small.{v} A] [IsLeftPerfectRing A]
    [IsLeftPerfectRing Aᵐᵒᵖ] : TauCeti.globalDimension.{v} Aᵐᵒᵖ = TauCeti.globalDimension.{v} A :=
  sorry

end Perfect

/-! ## Acceptance checks -/

/-- `ℚ` is a flat, not projective, `ℤ`-module. -/
theorem balancedFlat_rat_and_not_projective :
    Module.BalancedFlat ℤ ℚ ∧ ¬ Module.Projective ℤ ℚ :=
  sorry

/-- `ℤ` is not semiperfect: `ℤ ⧸ 2` has no projective cover. -/
theorem not_isSemiperfectRing_int : ¬ TauCeti.IsSemiperfectRing ℤ :=
  sorry

/-- The ideal `(X)` of a power series ring is not left T-nilpotent, so `PowerSeries k` is local,
hence semiperfect, and not left perfect. -/
theorem not_isLeftTNilpotent_span_X (k : Type u) [Field k] :
    ¬ IsLeftTNilpotent
      ((Ideal.span {PowerSeries.X} : Ideal (PowerSeries k)) : Set (PowerSeries k)) :=
  sorry


end TauCetiRoadmap.NoncommutativeFlatness
