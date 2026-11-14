module

import Mathlib
import TauCeti.LinearAlgebra.TensorProduct.Balanced.Basic
import TauCeti.Algebra.Category.ModuleCat.Algebra
import TauCeti.Algebra.Category.ModuleCat.Flat.FilteredFree
import TauCeti.Algebra.Category.ModuleCat.Projective.TensorHom
import TauCeti.Algebra.Module.AuslanderReiten.TensorCokernel
import TauCeti.Algebra.Module.CharacterModule.MulOpposite
import TauCeti.CategoryTheory.FinitelyPresentedFunctor.Basic
import TauCeti.RingTheory.MatlisDuality.Basic
import TauCeti.RingTheory.GlobalDimension
import TauCeti.RingTheory.Jacobson.Semiperfect
import TauCeti.Algebra.Module.ProjectiveCover.Basic
import TauCeti.Algebra.Module.Projective.FinitePresentation
import TauCeti.Algebra.Module.MinimalProjectivePresentation.Basic
import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic
import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.Semiperfect
import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Mul
import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Opposite
import TauCeti.CategoryTheory.Preadditive.Radical.Nilpotent
import TauCeti.CategoryTheory.Projective.Cover
import TauCeti.RingTheory.Jacobson.MulOpposite

/-!
# Flatness and homological dimensions of noncommutative rings: target signatures

**This file is not the roadmap and is not exhaustive.** The definitive document is
`README.md`. The statements here suggest Lean forms for particular milestones, so that
contributors and reviewers converge on names and signatures; discharging all of them finishes
neither a layer nor the roadmap. `sorry` is allowed in this human-owned roadmap library -- these
are goals, not proofs.

Layers as in `README.md`: 0 modules over a preadditive category and their tensor product; 1 `Tor`;
2 flat modules and flat functors; 3 flat dimension, global and weak global dimension, and
Auslander's theorem; 4 semiperfect and perfect rings and Bass's Theorem P.

Layers 0 and 1 are category-primary (README, "Conventions"). `C : Type u` is preadditive with
`Category.{v} C`. `ModCat C` (`Mod C`) is the full subcategory of additive functors
`Cᵒᵖ ⥤ AddCommGrpCat.{w}` (right modules), and `LeftModCat C` that of additive functors
`C ⥤ AddCommGrpCat.{w}`. For an `R`-linear `C` the `R`-structure of a module is derived: `r` acts
on `F(c)` by `F(r • 𝟙 c)`. `F ⊗_C G` is a coend in `ModuleCat R`; it exists when `C` is
`EssentiallySmall.{w}`. A ring `A` is the one-object category `SingleObj A`. Ring-level objects are
native: `M ⊗_A N` is `TauCeti.BalancedTensorProduct R A M N`, with `R`-linear maps, compared with
the categorical tensor product in 0.6. `Tor^C_n(F, G)` is the left derived functor of
`G ↦ F ⊗_C G` (Mathlib's classical `Functor.leftDerived`); ring `Tor` is `BalancedTor R A n`,
compared with `Tor` over `SingleObj A`.

Layer 2 is category-primary too. A left `C`-module `G` is flat (`LeftModCat.Flat`) when
`I ⊗_C G → G(X)` is injective for every finitely generated subfunctor `I ⊆ Hom(-, X)`; right modules
are flat as left `Cᵒᵖ`-modules. Ring flatness is the native class `Module.BalancedFlat`.

Layer 3 is category-primary as well. Flat dimension is defined by the vanishing of `Tor` on the
finitely presented cyclic right modules `Hom(-, X) ⧸ I`; the global dimension is defined for any
abelian category (`Abelian.globalDimension`), with Tau Ceti's ring `TauCeti.globalDimension` the
case `ModuleCat A`; the weak global dimension is `LeftModCat.weakGlobalDimension C`; Auslander's
theorem assumes that every representable `Hom(X, -)` is a Noetherian object. Layer 3 uses `R = ℤ`.

Layer 4 is category-primary as well. T-nilpotence is defined for an ideal of `C` (Tau Ceti's
`TauCeti.MorphismIdeal`), with Nakayama's lemma for all modules through `I · M`; `C` is semilocal,
semiperfect or left perfect through its endomorphism rings and its radical
`TauCeti.jacobsonRadicalIdeal C`; projective covers are Tau Ceti's essential epimorphisms
`TauCeti.IsEssentialEpi` from projective objects; Bass's Theorem P is `isLeftPerfect_tfae`, with the
ring version `isLeftPerfectRing_tfae` derived through `SingleObj A`. Rings keep native classes
(`IsSemilocalRing`, `IsLeftPerfectRing`) with bridges. 0.8 adds the finitely generated projective
modules `proj C` and the duality `Hom(-, C)`. A right `A`-module is a left `Aᵐᵒᵖ`-module and a
right ideal is a `Submodule Aᵐᵒᵖ A`.
Declarations that Tau Ceti already has are referred to by their full `TauCeti.` names.

Not stated here, and specified in prose in `README.md`: the transfer lemmas of 0.2, the `ULift`ed
representables for large `C`, the naturality of the isomorphisms in the variables not visible in
the statements (for example of the `Tor`–`Ext` duality), and the acceptance checks other than those
in the last section.
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

/-- **0.1** Additive functors are closed under colimits, computed objectwise (colimits commute with
finite biproducts). So `Mod C` and the left modules have the colimits of `AddCommGrpCat`. -/
instance {J : Type*} [Category J] [HasColimitsOfShape J AddCommGrpCat.{w}] :
    (additiveFunctor D AddCommGrpCat.{w}).IsClosedUnderColimitsOfShape J := sorry

end Closure

/-- **0.1** `Mod C` is abelian, by the closure properties and Mathlib's instance for full
subcategories (`Mathlib/CategoryTheory/Abelian/Subcategory.lean`); stated as an instance to cache
it. -/
noncomputable instance : Abelian (ModCat.{w} C) := inferInstance

/-- **0.1** Left `C`-modules form an abelian category. -/
noncomputable instance : Abelian (LeftModCat.{w} C) := inferInstance

/-- **0.1** `Mod C` has the colimits of `AddCommGrpCat`, from the closure under colimits. -/
instance (priority := high) {J : Type*} [Category J] [HasColimitsOfShape J AddCommGrpCat.{w}] :
    HasColimitsOfShape J (ModCat.{w} C) :=
  hasColimitsOfShape_of_closedUnderColimits _ _

/-- **0.1** Left `C`-modules have the colimits of `AddCommGrpCat`. -/
instance (priority := high) {J : Type*} [Category J] [HasColimitsOfShape J AddCommGrpCat.{w}] :
    HasColimitsOfShape J (LeftModCat.{w} C) :=
  hasColimitsOfShape_of_closedUnderColimits _ _

/-- **0.1** `Mod C` has enough projectives when `C` is `w`-small. -/
instance [EssentiallySmall.{w} C] : EnoughProjectives (ModCat.{w} C) := sorry

/-- **0.1** Left `C`-modules have enough projectives when `C` is `w`-small. -/
instance [EssentiallySmall.{w} C] : EnoughProjectives (LeftModCat.{w} C) := sorry

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

/-- **0.1** Left modules over an `R`-linear `C` form an `R`-linear category. -/
instance : Linear R (LeftModCat.{w} D) := sorry

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

/-- **0.3, ideals** For a two-sided ideal `I` of `C` (Tau Ceti's `TauCeti.MorphismIdeal`) and a left
module `M`, the subgroup `(I · M)(c)` of `M(c)` generated by the `M(f)(x)` with `f ∈ I(d, c)` and
`x ∈ M(d)`. For `C = SingleObj A` and a two-sided ideal `J` of `A` it is `J • ⊤`. -/
def MorphismIdeal.smul (I : TauCeti.MorphismIdeal C) (M : LeftModCat.{w} C) (c : C) :
    AddSubgroup (M.obj.obj c) :=
  AddSubgroup.closure
    {y | ∃ (d : C) (f : d ⟶ c) (_ : f ∈ I.hom d c) (x : M.obj.obj d), (M.obj.map f).hom x = y}

/-- **0.3, ideals** The right module `(C ⧸ I)(-, X) = Hom_{C ⧸ I}(-, X)`, through Tau Ceti's
quotient functor. For `I = J(C)` this is the right module `C ⧸ J` at `X` of 4.6. -/
noncomputable def MorphismIdeal.quotientYoneda (I : TauCeti.MorphismIdeal C) (X : C) :
    ModCat.{v} C :=
  ⟨I.quotientFunctor.op ⋙ preadditiveYoneda.obj (I.quotientFunctor.obj X),
    (inferInstance : (I.quotientFunctor.op ⋙ preadditiveYoneda.obj _).Additive)⟩

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

/-- **0.3, quotients by an ideal**: `(C ⧸ I)(-, X) ⊗_C M ≅ M(X) ⧸ (I · M)(X)` ([OR, Lemma 1.2] for a
right ideal of `Hom(-, X)`); right exactness and Yoneda. Used by 4.6. -/
noncomputable def tensorObjQuotientYonedaIso {C : Type u} [Category.{v} C] [Preadditive C]
    [EssentiallySmall.{v} C] (I : TauCeti.MorphismIdeal C) (X : C) (M : LeftModCat.{v} C) :
    tensorObj ℤ (MorphismIdeal.quotientYoneda I X) M ≅
      ModuleCat.of ℤ (M.obj.obj X ⧸ MorphismIdeal.smul I M X) :=
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

/-! ### 0.8 Finitely generated projective modules and duality -/

section Proj

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- **0.8** A left module is **finitely generated** if it is a quotient of a finite sum of
representables `Hom(Z₁, -) ⊕ ⋯ ⊕ Hom(Zₘ, -)`. -/
def LeftModCat.IsFinitelyGenerated (G : LeftModCat.{v} C) : Prop :=
  ∃ (m : ℕ) (Z : Fin m → C) (p : (∐ fun i ↦ (LeftModCat.coyoneda C).obj (op (Z i))) ⟶ G), Epi p

/-- **0.8** A right module is finitely generated when it is so as a left `Cᵒᵖ`-module: a quotient
of a finite sum of representables `Hom(-, Z_i)`. -/
abbrev ModCat.IsFinitelyGenerated (F : ModCat.{v} C) : Prop :=
  LeftModCat.IsFinitelyGenerated (C := Cᵒᵖ) F

variable (C) in
/-- **0.8** The finitely generated projective left modules. -/
def LeftModCat.proj : ObjectProperty (LeftModCat.{v} C) :=
  fun G ↦ Projective G ∧ G.IsFinitelyGenerated

variable (C) in
/-- **0.8** `proj C`: the finitely generated projective right modules, so that `C ⊆ proj C`
covariantly by Yoneda. Defined as `LeftModCat.proj Cᵒᵖ`, the pattern of `ModCat.Flat`; the left
ones, `LeftModCat.proj C`, are `proj Cᵒᵖ` up to `Cᵒᵖᵒᵖ = C`. -/
abbrev ModCat.proj : ObjectProperty (ModCat.{v} C) :=
  LeftModCat.proj Cᵒᵖ

/-- **0.8** Finitely generated projective modules are closed under finite biproducts. -/
instance : HasFiniteBiproducts (LeftModCat.proj C).FullSubcategory := sorry

/-- **0.8** Idempotents split in `proj C`: a retract of a finitely generated projective module is
finitely generated projective. -/
instance : IsIdempotentComplete (LeftModCat.proj C).FullSubcategory := sorry

/-- **0.8** Representable right modules are finitely generated projective. -/
theorem ModCat.proj_yoneda_obj (X : C) : ModCat.proj C ((ModCat.yoneda C).obj X) :=
  sorry

/-- **0.8** Finite sums of representables are finitely generated projective. -/
theorem ModCat.proj_sigma_yoneda {q : ℕ} (Y : Fin q → C) :
    ModCat.proj C (∐ fun j ↦ (ModCat.yoneda C).obj (Y j)) :=
  sorry

/-- **0.8** Representable left modules are finitely generated projective. -/
theorem LeftModCat.proj_coyoneda_obj (X : Cᵒᵖ) :
    LeftModCat.proj C ((LeftModCat.coyoneda C).obj X) :=
  sorry

variable (C) in
/-- **0.8, Yoneda** `C ⥤ proj C`, `X ↦ Hom(-, X)`; fully faithful, so `End Hom(-, X) = End X`. -/
def ModCat.projYoneda : C ⥤ (ModCat.proj C).FullSubcategory :=
  ObjectProperty.lift _ (ModCat.yoneda C) ModCat.proj_yoneda_obj

variable (C) in
/-- **0.8** `Cᵒᵖ ⥤ LeftModCat.proj C`, `X ↦ Hom(X, -)`. -/
def LeftModCat.projCoyoneda : Cᵒᵖ ⥤ (LeftModCat.proj C).FullSubcategory :=
  ObjectProperty.lift _ (LeftModCat.coyoneda C) LeftModCat.proj_coyoneda_obj

instance : (ModCat.projYoneda C).Full := sorry

instance : (ModCat.projYoneda C).Faithful := sorry

variable (C) in
/-- **0.8** `proj C ≌ Karoubi (Mat_ C)`: every finitely generated projective module is a summand of
a finite sum of representables, and Yoneda is fully faithful. Tau Ceti's
`TauCeti.projectivizationFunctor` is the one-object pattern. -/
noncomputable def ModCat.projEquivKaroubiMat :
    (ModCat.proj C).FullSubcategory ≌ CategoryTheory.Idempotents.Karoubi (Mat_ C) :=
  sorry

/-- **0.8** For an additive, idempotent-complete `C`, Yoneda `C ⥤ proj C` is an equivalence. -/
instance [HasFiniteBiproducts C] [IsIdempotentComplete C] : (ModCat.projYoneda C).IsEquivalence :=
  sorry

variable (C) in
/-- **0.8, duality** `(-)^∨ = Hom(-, C) : (proj C)ᵒᵖ ≌` the finitely generated projective left
modules, `Hom(-, X) ↦ Hom(X, -)`. Built from the two Karoubi equivalences and
`(Mat_ C)ᵒᵖ ≌ Mat_ Cᵒᵖ` (transposed matrices). -/
noncomputable def ModCat.projDual :
    (ModCat.proj C).FullSubcategoryᵒᵖ ≌ (LeftModCat.proj C).FullSubcategory :=
  sorry

/-- **0.8** The dual of `Hom(-, X)` is `Hom(X, -)`. -/
noncomputable def ModCat.projDualYonedaIso (X : C) :
    (ModCat.projDual C).functor.obj (op ((ModCat.projYoneda C).obj X)) ≅
      (LeftModCat.projCoyoneda C).obj (op X) :=
  sorry

end Proj

/-- **0.8, rings** Finitely generated projective modules have finite biproducts. -/
instance (A : Type u) [Ring A] :
    HasFiniteBiproducts (TauCeti.finiteProjectiveModules A).FullSubcategory :=
  sorry

/-- **0.8, rings** `Hom_A(-, A)` from finitely generated projective left modules to finitely
generated projective right modules (Tau Ceti's `TauCeti.finiteProjectiveModules`). Mathlib's
`Module.Dual A P` is defined over any semiring, but its API is commutative; Tau Ceti's
`TauCeti.AuslanderReitenTranspose` already uses it as a right module. -/
noncomputable def finiteProjectiveModulesDual (A : Type u) [Ring A] :
    (TauCeti.finiteProjectiveModules A).FullSubcategoryᵒᵖ ≌
      (TauCeti.finiteProjectiveModules Aᵐᵒᵖ).FullSubcategory :=
  sorry

/-! ## Layer 1: `Tor`

`Tor` is category-primary. `Tor^C_n(F, -)` is Mathlib's classical `Functor.leftDerived` of
`G ↦ F ⊗_C G`, derived in the left-module variable, as Mathlib's `CategoryTheory.Tor`. There is one
`Tor`: the version that resolves the right module is `Tor` over `Cᵒᵖ` through the swap of 0.5. For
rings, `BalancedTor R A n` is the left derived functor of the ring bifunctor of 0.6, compared with
`Tor` over `SingleObj A`. For finitely presented `X`, the stable `Hom(X, N)` is `Tor_1(Tr X, N)`
(1.4). Layer 3 uses `R = ℤ`. -/

/-! ### 1.1 Definition -/

namespace ModCat

section Tor

variable (R : Type*) [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  [EssentiallySmall.{w} C]

/-- **1.1** `Tor^C_n(F, G)`: the `n`-th left derived functor of `G ↦ F ⊗_C G` (Mathlib's
classical `Functor.leftDerived`, as in `CategoryTheory.Tor`), a bifunctor to `ModuleCat R`. -/
noncomputable def tor (n : ℕ) : ModCat.{w} C ⥤ LeftModCat.{w} C ⥤ ModuleCat.{w} R where
  obj F := ((tensor R).obj F).leftDerived n
  map f := NatTrans.leftDerived ((tensor R).map f) n

/-- **1.1** `Tor₀` is the tensor product: `Functor.leftDerivedZeroIsoSelf` and right exactness
(0.3). -/
noncomputable def torZeroIso : tor.{w} R (C := C) 0 ≅ tensor R :=
  sorry

/-- **1.1** `Tor_{n+1}(F, G) = 0` for a projective left module `G`. -/
theorem isZero_tor_succ_of_projective (F : ModCat.{w} C) (G : LeftModCat.{w} C) [Projective G]
    (n : ℕ) : IsZero (((tor R (n + 1)).obj F).obj G) :=
  Functor.isZero_leftDerived_obj_projective_succ _ _ _

/-- **1.1** `Tor` from any projective resolution `P` of the left module: the homology of
`F ⊗_C P`. -/
noncomputable def torObjIsoHomology (F : ModCat.{w} C) {G : LeftModCat.{w} C}
    (P : ProjectiveResolution G) (n : ℕ) :
    ((tor R n).obj F).obj G ≅
      (HomologicalComplex.homologyFunctor _ _ n).obj
        ((((tensor R).obj F).mapHomologicalComplex _).obj P.complex) :=
  P.isoLeftDerivedObj _ n

/-- **1.1** `Tor` is additive in the right-module variable (`NatTrans.leftDerived_add`). -/
instance (G : LeftModCat.{w} C) (n : ℕ) : ((tor R n).flip.obj G).Additive :=
  sorry

/-- **1.1** `Tor` is `R`-linear in the right-module variable. -/
instance (G : LeftModCat.{w} C) (n : ℕ) : ((tor R n).flip.obj G).Linear R :=
  sorry

/-- **1.1** `Tor` is `R`-linear in the left-module variable. -/
instance (F : ModCat.{w} C) (n : ℕ) : ((tor R n).obj F).Linear R :=
  sorry

end Tor

end ModCat

/-- **1.1** `Small.{v} Aᵐᵒᵖ` from `Small.{v} A`, so that right modules have projective
resolutions in `ModuleCat.{v} Aᵐᵒᵖ`. -/
instance small_mulOpposite (A : Type u) [Small.{v} A] : Small.{v} Aᵐᵒᵖ :=
  small_of_injective MulOpposite.unop_injective

section BalancedTor

variable (R : Type t) [CommRing R] (A : Type u) [Ring A] [Algebra R A] [Small.{v} A]

/-- **1.1, rings** `Tor_n^A(M, N)`: the left derived functor of the ring bifunctor of 0.6 in the
left-module variable `N`, the shape of Mathlib's `CategoryTheory.Tor`. -/
noncomputable def BalancedTor (n : ℕ) :
    ModuleCat.{v} Aᵐᵒᵖ ⥤ ModuleCat.{v} A ⥤ ModuleCat.{v} R where
  obj M := ((BalancedTensorProduct.functor R A).obj M).leftDerived n
  map f := NatTrans.leftDerived ((BalancedTensorProduct.functor R A).map f) n

/-- **1.1, rings** `Tor_0` is the tensor product. -/
noncomputable def balancedTorZeroIso :
    BalancedTor.{v} R A 0 ≅ BalancedTensorProduct.functor.{v} R A :=
  sorry

/-- **1.1, rings** Ring `Tor` is `Tor` over the one-object category `SingleObj A`, through the
equivalences of 0.2. -/
noncomputable def balancedTorIsoTorSingleObj (n : ℕ) :
    BalancedTor.{v} R A n ≅
      (moduleCatMulOppositeEquivModCat.{v} A).functor ⋙ ModCat.tor R n ⋙
        (Functor.whiskeringLeft _ _ _).obj (moduleCatEquivLeftModCat.{v} A).functor :=
  sorry

variable {R A}

/-- **1.1, rings** Higher `Tor` vanishes at a projective left module. -/
theorem isZero_balancedTor_succ_of_projective (M : ModuleCat.{v} Aᵐᵒᵖ) (N : ModuleCat.{v} A)
    [Projective N] (n : ℕ) : IsZero (((BalancedTor R A (n + 1)).obj M).obj N) :=
  Functor.isZero_leftDerived_obj_projective_succ _ _ _

end BalancedTor

/-! ### 1.2 Long exact sequences in the underived variable -/

section LongExact

open ModCat

variable (R : Type*) [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  [EssentiallySmall.{w} C] {S : ShortComplex (ModCat.{w} C)}

/-- **1.2** The connecting map `Tor_{n+1}(F₃, G) → Tor_n(F₁, G)` of a short exact sequence
`0 → F₁ → F₂ → F₃ → 0` of right modules: the homology connecting map of the short exact sequence
of complexes `Fᵢ ⊗_C Q`, `Q` a projective resolution of `G` (exact termwise by 0.3 and 0.4). -/
noncomputable def ShortComplex.ShortExact.torδ (hS : S.ShortExact) (G : LeftModCat.{w} C)
    (n : ℕ) : ((tor R (n + 1)).obj S.X₃).obj G ⟶ ((tor R n).obj S.X₁).obj G :=
  sorry

/-- **1.2** Exactness at `Tor_n(F₁, G)`. -/
theorem tor_exact₁ (hS : S.ShortExact) (G : LeftModCat.{w} C) (n : ℕ) :
    Function.Exact (ShortComplex.ShortExact.torδ R hS G n).hom
      (((tor R n).map S.f).app G).hom :=
  sorry

/-- **1.2** Exactness at `Tor_n(F₂, G)`. -/
theorem tor_exact₂ (hS : S.ShortExact) (G : LeftModCat.{w} C) (n : ℕ) :
    Function.Exact (((tor R n).map S.f).app G).hom (((tor R n).map S.g).app G).hom :=
  sorry

/-- **1.2** Exactness at `Tor_{n+1}(F₃, G)`. -/
theorem tor_exact₃ (hS : S.ShortExact) (G : LeftModCat.{w} C) (n : ℕ) :
    Function.Exact (((tor R (n + 1)).map S.g).app G).hom
      (ShortComplex.ShortExact.torδ R hS G n).hom :=
  sorry

end LongExact

section BalancedTorLongExact

variable (R : Type t) [CommRing R] {A : Type u} [Ring A] [Algebra R A] [Small.{v} A]
  {S : ShortComplex (ModuleCat.{v} Aᵐᵒᵖ)}

/-- **1.2, rings** The connecting map `Tor_{n+1}(M₃, N) → Tor_n(M₁, N)` of a short exact sequence
of right modules. -/
noncomputable def ShortComplex.ShortExact.balancedTorδ (hS : S.ShortExact) (N : ModuleCat.{v} A)
    (n : ℕ) :
    ((BalancedTor R A (n + 1)).obj S.X₃).obj N ⟶ ((BalancedTor R A n).obj S.X₁).obj N :=
  sorry

/-- **1.2, rings** Exactness at `Tor_n(M₁, N)`. -/
theorem balancedTor_exact₁ (hS : S.ShortExact) (N : ModuleCat.{v} A) (n : ℕ) :
    Function.Exact (ShortComplex.ShortExact.balancedTorδ R hS N n).hom
      (((BalancedTor R A n).map S.f).app N).hom :=
  sorry

/-- **1.2, rings** Exactness at `Tor_n(M₂, N)`. -/
theorem balancedTor_exact₂ (hS : S.ShortExact) (N : ModuleCat.{v} A) (n : ℕ) :
    Function.Exact (((BalancedTor R A n).map S.f).app N).hom
      (((BalancedTor R A n).map S.g).app N).hom :=
  sorry

/-- **1.2, rings** Exactness at `Tor_{n+1}(M₃, N)`. -/
theorem balancedTor_exact₃ (hS : S.ShortExact) (N : ModuleCat.{v} A) (n : ℕ) :
    Function.Exact (((BalancedTor R A (n + 1)).map S.g).app N).hom
      (ShortComplex.ShortExact.balancedTorδ R hS N n).hom :=
  sorry

end BalancedTorLongExact

/-! ### 1.3 Balance -/

namespace ModCat

section Balance

variable (R : Type*) [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  [EssentiallySmall.{w} C]

/-- **1.3, balance**: `Tor^C_n(F, G) ≅ Tor^{Cᵒᵖ}_n(G, F)`, with `G` a right `Cᵒᵖ`-module and `F`
a left `Cᵒᵖ`-module as in 0.5. Route: the bicomplex `P ⊗_C Q` of projective resolutions and Tau
Ceti's `HomologicalComplex₂.quasiIso_totalAugmentation_of_rows` for it and its flip. -/
noncomputable def torBalanceIso (n : ℕ) :
    tor.{w} R (C := C) n ≅ (LeftModCat.toModCatOp C ⋙ tor R (C := Cᵒᵖ) n).flip :=
  sorry

/-- **1.3** Higher `Tor` vanishes at a projective right module (balance and 1.1 over `Cᵒᵖ`). -/
theorem isZero_tor_succ_of_projective_left (F : ModCat.{w} C) [Projective F]
    (G : LeftModCat.{w} C) (n : ℕ) : IsZero (((tor R (n + 1)).obj F).obj G) :=
  sorry

end Balance

end ModCat

section BalanceLongExact

open ModCat

variable (R : Type*) [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  [EssentiallySmall.{w} C] {S : ShortComplex (LeftModCat.{w} C)}

/-- **1.3** The connecting map `Tor_{n+1}(F, G₃) → Tor_n(F, G₁)` of a short exact sequence of left
modules: 1.2 over `Cᵒᵖ`, transported by the balance. -/
noncomputable def ShortComplex.ShortExact.torδ' (F : ModCat.{w} C) (hS : S.ShortExact) (n : ℕ) :
    ((tor R (n + 1)).obj F).obj S.X₃ ⟶ ((tor R n).obj F).obj S.X₁ :=
  sorry

/-- **1.3** Exactness at `Tor_n(F, G₁)`. -/
theorem tor_exact₁' (F : ModCat.{w} C) (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (ShortComplex.ShortExact.torδ' R F hS n).hom
      (((tor R n).obj F).map S.f).hom :=
  sorry

/-- **1.3** Exactness at `Tor_n(F, G₂)`. -/
theorem tor_exact₂' (F : ModCat.{w} C) (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (((tor R n).obj F).map S.f).hom (((tor R n).obj F).map S.g).hom :=
  sorry

/-- **1.3** Exactness at `Tor_{n+1}(F, G₃)`. -/
theorem tor_exact₃' (F : ModCat.{w} C) (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (((tor R (n + 1)).obj F).map S.g).hom
      (ShortComplex.ShortExact.torδ' R F hS n).hom :=
  sorry

end BalanceLongExact

section BalancedTorBalance

variable (R : Type t) [CommRing R] (A : Type u) [Ring A] [Algebra R A] [Small.{v} A]

/-- **1.3, rings: swap** `Tor_n^A(M, N) ≅ Tor_n^{Aᵐᵒᵖ}(N, M)`, with `N` a right `Aᵐᵒᵖ`-module
through `RingEquiv.opOp A`: 1.1's comparison and the balance at `SingleObj A`. -/
noncomputable def balancedTorSwapIso (n : ℕ) :
    BalancedTor.{v} R A n ≅
      (ModuleCat.restrictScalars.{v} (RingEquiv.opOp A).symm.toRingHom ⋙
        BalancedTor.{v} R Aᵐᵒᵖ n).flip :=
  sorry

variable {R A}

/-- **1.3, rings** Higher `Tor` vanishes at a projective right module. -/
theorem isZero_balancedTor_succ_of_projective_left (M : ModuleCat.{v} Aᵐᵒᵖ) [Projective M]
    (N : ModuleCat.{v} A) (n : ℕ) : IsZero (((BalancedTor R A (n + 1)).obj M).obj N) :=
  sorry

variable (R) {S : ShortComplex (ModuleCat.{v} A)}

/-- **1.3, rings** The connecting map `Tor_{n+1}(M, N₃) → Tor_n(M, N₁)` of a short exact sequence
of left modules. -/
noncomputable def ShortComplex.ShortExact.balancedTorδ' (M : ModuleCat.{v} Aᵐᵒᵖ)
    (hS : S.ShortExact) (n : ℕ) :
    ((BalancedTor R A (n + 1)).obj M).obj S.X₃ ⟶ ((BalancedTor R A n).obj M).obj S.X₁ :=
  sorry

/-- **1.3, rings** Exactness at `Tor_n(M, N₁)`. -/
theorem balancedTor_exact₁' (M : ModuleCat.{v} Aᵐᵒᵖ) (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (ShortComplex.ShortExact.balancedTorδ' R M hS n).hom
      (((BalancedTor R A n).obj M).map S.f).hom :=
  sorry

/-- **1.3, rings** Exactness at `Tor_n(M, N₂)`. -/
theorem balancedTor_exact₂' (M : ModuleCat.{v} Aᵐᵒᵖ) (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (((BalancedTor R A n).obj M).map S.f).hom
      (((BalancedTor R A n).obj M).map S.g).hom :=
  sorry

/-- **1.3, rings** Exactness at `Tor_{n+1}(M, N₃)`. -/
theorem balancedTor_exact₃' (M : ModuleCat.{v} Aᵐᵒᵖ) (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (((BalancedTor R A (n + 1)).obj M).map S.g).hom
      (ShortComplex.ShortExact.balancedTorδ' R M hS n).hom :=
  sorry

end BalancedTorBalance

/-! ### 1.4 `Tor` of the transpose -/

section Transpose

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- **1.4** The map `⊕_j Hom(-, Y j) → ⊕_i Hom(-, Z i)` given by a matrix `α j i : Y j ⟶ Z i`;
its cokernel is a finitely presented right module, and every finitely presented right module is
such a cokernel. -/
noncomputable def ModCat.matrixMap {p q : ℕ} {Y : Fin q → C} {Z : Fin p → C}
    (α : ∀ j i, Y j ⟶ Z i) :
    (∐ fun j ↦ (ModCat.yoneda C).obj (Y j)) ⟶ ∐ fun i ↦ (ModCat.yoneda C).obj (Z i) :=
  Limits.Sigma.desc fun j ↦
    ∑ i, (ModCat.yoneda C).map (α j i) ≫ Limits.Sigma.ι (fun i ↦ (ModCat.yoneda C).obj (Z i)) i

/-- **1.4** The Auslander–Bridger transpose of a map `f : P₁ ⟶ P₀` of finitely generated projective
right modules: `Tr = coker (P₀^∨ → P₁^∨)`, with the duality `(-)^∨ = Hom(-, C)` of 0.8; a left
module. -/
noncomputable def ModCat.transpose {P₁ P₀ : (ModCat.proj C).FullSubcategory} (f : P₁ ⟶ P₀) :
    LeftModCat.{v} C :=
  cokernel ((ModCat.projDual C).functor.map f.op).hom

/-- **1.4** A finite sum of representables `⊕_j Hom(-, Y j)` as an object of `proj C`. -/
noncomputable def ModCat.projSigma {q : ℕ} (Y : Fin q → C) : (ModCat.proj C).FullSubcategory :=
  ⟨∐ fun j ↦ (ModCat.yoneda C).obj (Y j), ModCat.proj_sigma_yoneda Y⟩

/-- **1.4** The cokernel of the transposed matrix `⊕_i Hom(Z i, -) → ⊕_j Hom(Y j, -)`, a left
module. -/
noncomputable def ModCat.matrixTranspose {p q : ℕ} {Y : Fin q → C} {Z : Fin p → C}
    (α : ∀ j i, Y j ⟶ Z i) : LeftModCat.{v} C :=
  cokernel (Limits.Sigma.desc fun i ↦
    ∑ j, (LeftModCat.coyoneda C).map (α j i).op ≫
      Limits.Sigma.ι (fun j ↦ (LeftModCat.coyoneda C).obj (op (Y j))) j)

/-- **1.4, the matrix description**: the transpose of `matrixMap α` is the cokernel of the
transposed matrix, since the dual of `Hom(-, X)` is `Hom(X, -)` (0.8). -/
noncomputable def ModCat.transposeMatrixIso {p q : ℕ} {Y : Fin q → C} {Z : Fin p → C}
    (α : ∀ j i, Y j ⟶ Z i) :
    ModCat.transpose
        (ObjectProperty.homMk (ModCat.matrixMap α) : ModCat.projSigma Y ⟶ ModCat.projSigma Z) ≅
      ModCat.matrixTranspose α :=
  sorry

variable [EssentiallySmall.{v} C]

/-- **1.4, `Tor` of the transpose** ([Auslander78, I, Prop. 3.2]): for the finitely presented right
module `X = coker f` and any right module `N`, the stable `Hom(X, N)` (Tau Ceti's projective stable
category of `Mod C`) is `Tor_1(N, Tr X)`. Route: for `0 → ΩN → P → N → 0` with `P` projective, the
snake lemma identifies the cokernel of `Hom(X, P) → Hom(X, N)` with the kernel of `H(ΩN) → H(P)`,
where `H(M) = coker (Hom(P₀, M) → Hom(P₁, M)) ≅ M ⊗_C Tr X`; then 1.2. -/
noncomputable def ModCat.stableHomEquivTorTranspose {P₁ P₀ : (ModCat.proj C).FullSubcategory}
    (f : P₁ ⟶ P₀) (N : ModCat.{v} C) :
    ((TauCeti.ExactStructure.projectiveStableFunctor
        (TauCeti.ExactStructure.abelian (ModCat.{v} C))).obj (cokernel f.hom) ⟶
      (TauCeti.ExactStructure.projectiveStableFunctor
        (TauCeti.ExactStructure.abelian (ModCat.{v} C))).obj N) ≃+
      ((ModCat.tor ℤ 1).obj N).obj (ModCat.transpose f) :=
  sorry

end Transpose

section BalancedTorTranspose

open scoped ModuleCat.Algebra

variable (R : Type t) [CommRing R] {A : Type u} [Ring A] [Algebra R A]
  {P₀ P₁ : Type u} [AddCommGroup P₀] [Module A P₀] [Module.Finite A P₀] [Module.Projective A P₀]
  [AddCommGroup P₁] [Module A P₁] [Module.Finite A P₁] [Module.Projective A P₁]

/-- **1.4, rings: `Tor` of the transpose** ([Auslander78, I, Prop. 3.2]): for a presentation
`P₁ → P₀ → X → 0` by finite projectives, the stable `Hom_A(X, N)` (Tau Ceti's projective stable
category) is `Tor_1^A(Tr X, N)`, with Tau Ceti's `AuslanderReitenTranspose`. Route: the snake lemma
`Function.Exact.contravariantDefectEquivKer` and Tau Ceti's
`LinearMap.auslanderReitenTransposeTensorEquivCokernel`, applied to `0 → ΩN → P → N → 0`, and the
long exact sequence of 1.3. -/
noncomputable def stableHomEquivBalancedTorTranspose {X : ModuleCat.{u} A} {f : P₁ →ₗ[A] P₀}
    {π : P₀ →ₗ[A] X} (hfπ : Function.Exact f π) (hπ : Function.Surjective π)
    (N : ModuleCat.{u} A) :
    ((TauCeti.ExactStructure.projectiveStableFunctor
        (TauCeti.ExactStructure.abelian (ModuleCat.{u} A))).obj X ⟶
      (TauCeti.ExactStructure.projectiveStableFunctor
        (TauCeti.ExactStructure.abelian (ModuleCat.{u} A))).obj N) ≃ₗ[R]
      ((BalancedTor R A 1).obj (ModuleCat.of Aᵐᵒᵖ (TauCeti.AuslanderReitenTranspose f))).obj N :=
  sorry

end BalancedTorTranspose

/-! ### 1.5 `Tor`–`Ext` duality -/

namespace ModCat

section Duality

variable (R : Type*) [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  [EssentiallySmall.{w} C]

/-- **1.5** `Ext` groups of `Mod C` live in `Type w` (Mathlib's `hasExt_of_enoughProjectives`, as
for `ModuleCat`). -/
instance : HasExt.{w} (ModCat.{w} C) :=
  sorry

/-- **1.5, `Tor`–`Ext` duality**: for an injective `R`-module `E`,
`Hom_R(Tor_n^C(F, G), E) ≅ Ext^n(F, G^E)`, `R`-linearly, with Mathlib's `Abelian.Ext`. Route:
resolve `F` (by the balance), the adjunction of 0.7 termwise, and Mathlib's
`ProjectiveResolution.extEquivCohomologyClass`. -/
noncomputable def torExtDualityEquiv (E : ModuleCat.{w} R) [Injective E] (F : ModCat.{w} C)
    (G : LeftModCat.{w} C) (n : ℕ) :
    ((((tor R n).obj F).obj G) ⟶ E) ≃ₗ[R]
      Abelian.Ext.{w} F ((LeftModCat.dual R E).obj (op G)) n :=
  sorry

end Duality

end ModCat

section BalancedTorDuality

open scoped ModuleCat.Algebra

variable {R : Type t} [CommRing R] {A : Type u} [Ring A] [Algebra R A] [Small.{v} A]

/-- **1.5, rings**: `Hom_R(Tor_n^A(M, N), E) ≅ Ext^n_{Aᵐᵒᵖ}(M, Hom_R(N, E))` for an injective
`R`-module `E` (`R = ℤ`, `E = ℚ ⧸ ℤ`: [Lambek, p. 241]). -/
noncomputable def balancedTorExtDualityEquiv (E : ModuleCat.{v} R) [Injective E]
    (M : ModuleCat.{v} Aᵐᵒᵖ) (N : ModuleCat.{v} A) (n : ℕ) :
    ((((BalancedTor R A n).obj M).obj N) ⟶ E) ≃ₗ[R]
      Abelian.Ext.{v} M ((BalancedTensorProduct.homRight R A N).obj E) n :=
  sorry

end BalancedTorDuality

/-! ### 1.6 Comparisons and first computations -/

/-- **1.6, commutative rings**: over a commutative ring, `BalancedTor R R` is Mathlib's
`CategoryTheory.Tor`. -/
noncomputable def balancedTorIsoTor (R : Type u) [CommRing R] (n : ℕ) :
    ModuleCat.restrictScalars.{u} (RingEquiv.toOpposite R).symm.toRingHom ⋙ BalancedTor.{u} R R n ≅
      Tor (ModuleCat.{u} R) n :=
  sorry

/-- **1.6** With the balance, Mathlib's two `Tor`s on `ModuleCat R` agree, the comparison that
`Mathlib/CategoryTheory/Monoidal/Tor.lean` leaves open. -/
noncomputable def torIsoTor' (R : Type u) [CommRing R] (n : ℕ) :
    Tor (ModuleCat.{u} R) n ≅ Tor' (ModuleCat.{u} R) n :=
  sorry

namespace ModCat

variable (R : Type*) [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  [EssentiallySmall.{w} C]

/-- **1.6, change of base** along `R → R'`, when the `R`-structure of `C` comes from the
`R'`-structure (0.3). -/
noncomputable def torRestrictScalarsIso {R' : Type*} [CommRing R'] [Algebra R R'] [Linear R' C]
    (h : ∀ (X Y : C) (r : R) (f : X ⟶ Y), r • f = algebraMap R R' r • f) (n : ℕ)
    (F : ModCat.{w} C) (G : LeftModCat.{w} C) :
    (ModuleCat.restrictScalars (algebraMap R R')).obj (((tor R' n).obj F).obj G) ≅
      ((tor R n).obj F).obj G :=
  sorry

/-- **1.6, independence of `R`**: the `R`-`Tor` and the `ℤ`-`Tor` have the same underlying
groups. -/
noncomputable def torIntIso (n : ℕ) (F : ModCat.{w} C) (G : LeftModCat.{w} C) :
    (ModuleCat.restrictScalars (algebraMap ℤ R)).obj (((tor R n).obj F).obj G) ≅
      ((tor ℤ n).obj F).obj G :=
  sorry

end ModCat

section BalancedTorBase

variable (R : Type t) [CommRing R] {A : Type u} [Ring A] [Algebra R A] [Small.{v} A]

/-- **1.6, rings: change of base** along `R → R' → A`. -/
noncomputable def balancedTorRestrictScalarsIso (R' : Type t) [CommRing R'] [Algebra R R']
    [Algebra R' A] [IsScalarTower R R' A] (n : ℕ) (M : ModuleCat.{v} Aᵐᵒᵖ) (N : ModuleCat.{v} A) :
    (ModuleCat.restrictScalars (algebraMap R R')).obj (((BalancedTor R' A n).obj M).obj N) ≅
      ((BalancedTor R A n).obj M).obj N :=
  sorry

/-- **1.6, rings: independence of `R`.** -/
noncomputable def balancedTorIntIso (n : ℕ) (M : ModuleCat.{v} Aᵐᵒᵖ) (N : ModuleCat.{v} A) :
    (ModuleCat.restrictScalars (algebraMap ℤ R)).obj (((BalancedTor R A n).obj M).obj N) ≅
      ((BalancedTor ℤ A n).obj M).obj N :=
  sorry

end BalancedTorBase

/-- **1.6, cyclic modules**: for a right ideal `I` and a left ideal `K`,
`Tor_1^A(A ⧸ I, A ⧸ K) ≃+ (I ∩ K) ⧸ IK`, with `IK` the additive subgroup generated by products
([Weibel, Exer. 3.1.3, p. 68]). -/
noncomputable def balancedTorOneQuotientEquiv (A : Type u) [Ring A] (I : Submodule Aᵐᵒᵖ A)
    (K : Ideal A) :
    (((BalancedTor.{u} ℤ A 1).obj (ModuleCat.of Aᵐᵒᵖ (A ⧸ I))).obj (ModuleCat.of A (A ⧸ K))) ≃+
      ↥(I.toAddSubgroup ⊓ K.toAddSubgroup) ⧸
        (AddSubgroup.closure (Set.image2 (· * ·) (I : Set A) (K : Set A))).addSubgroupOf
          (I.toAddSubgroup ⊓ K.toAddSubgroup) :=
  sorry

/-! ### 1.7 Categories with finitely many objects -/

/-- **1.7** The category algebra `⊕_{x,y} Hom(x, y)` of a category with finitely many objects
([Mitchell, §7, p. 33]): families `a x y : x ⟶ y`, with `(a * b) x z = ∑ y, b x y ≫ a y z` and
the identities on the diagonal as unit. The product follows Mathlib's `SingleObj` convention
`f ≫ g = g * f`, so `CategoryAlgebra (SingleObj A) ≅ A`. -/
def CategoryAlgebra (C : Type u) [Category.{v} C] : Type (max u v) :=
  ∀ x y : C, x ⟶ y

section CategoryAlgebra

variable (C : Type u) [Category.{v} C] [Preadditive C] [Fintype C] [DecidableEq C]

/-- **1.7** The ring structure of the category algebra. -/
instance : Ring (CategoryAlgebra C) :=
  sorry

/-- **1.7** For an `R`-linear `C`, the category algebra is an `R`-algebra. -/
instance (R : Type*) [CommRing R] [Linear R C] : Algebra R (CategoryAlgebra C) :=
  sorry

/-- **1.7** Left `C`-modules are left modules over the category algebra, `G ↦ ⊕_x G(x)`
([Mitchell, Thm. 7.1, pp. 33–35]; the pattern of Tau Ceti's `quiverRepEquivalence`). -/
noncomputable def leftModCatEquivCategoryAlgebra :
    LeftModCat.{w} C ≌ ModuleCat.{w} (CategoryAlgebra C) :=
  sorry

/-- **1.7** Right `C`-modules are right modules over the category algebra. -/
noncomputable def modCatEquivCategoryAlgebra :
    ModCat.{w} C ≌ ModuleCat.{w} (CategoryAlgebra C)ᵐᵒᵖ :=
  sorry

/-- **1.7** The equivalences carry the tensor product over `C` to the balanced tensor product
over the category algebra ([Mitchell, §7, p. 37]). -/
noncomputable def tensorObjCategoryAlgebraIso (R : Type t) [CommRing R] [Linear R C]
    [EssentiallySmall.{w} C] (F : ModCat.{w} C) (G : LeftModCat.{w} C) :
    ModCat.tensorObj R F G ≅
      ((BalancedTensorProduct.functor R (CategoryAlgebra C)).obj
        ((modCatEquivCategoryAlgebra C).functor.obj F)).obj
          ((leftModCatEquivCategoryAlgebra C).functor.obj G) :=
  sorry

/-- **1.7** The equivalences carry `Tor` over `C` to `Tor` over the category algebra
([Mitchell, §7, p. 37, (1)]). -/
noncomputable def torCategoryAlgebraIso (R : Type t) [CommRing R] [Linear R C]
    [EssentiallySmall.{w} C] [Small.{w} (CategoryAlgebra C)] (n : ℕ) :
    ModCat.tor.{w} R (C := C) n ≅
      (modCatEquivCategoryAlgebra.{w} C).functor ⋙ BalancedTor R (CategoryAlgebra C) n ⋙
        (Functor.whiskeringLeft _ _ _).obj (leftModCatEquivCategoryAlgebra.{w} C).functor :=
  sorry

end CategoryAlgebra

/-! ## Layer 2: flat modules and flat functors

Flatness is category-primary. A left `C`-module `G` is flat when it passes the ideal test: for every
object `X` and every finitely generated subfunctor `I ⊆ Hom(-, X)`, the map
`I ⊗_C G → Hom(-, X) ⊗_C G ≅ G(X)` is injective. A right module is flat when it is flat as a left
`Cᵒᵖ`-module (0.5). The definition uses `R = ℤ`; flatness does not depend on `R` (2.1). It is
stated for modules in the universe `v` of the morphisms of `C`, where the representables live
(0.1); an `EssentiallySmall.{w} C` passes to a small model. Rings keep a native class
`Module.BalancedFlat`, compared with flatness over `SingleObj A`. -/

/-! ### 2.1 Definition -/

section FlatDef

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- **2.1** The subfunctor of `Hom(-, X)` generated by finitely many morphisms `β j : Y j ⟶ X`: the
image of `⊕_j Hom(-, Y j) → Hom(-, X)`. These are the finitely generated subfunctors of
`Hom(-, X)`. -/
noncomputable def ModCat.yonedaSpan {X : C} {n : ℕ} {Y : Fin n → C} (β : ∀ j, Y j ⟶ X) :
    Subobject ((ModCat.yoneda C).obj X) :=
  imageSubobject (Limits.Sigma.desc fun j ↦ (ModCat.yoneda C).map (β j))

variable [EssentiallySmall.{v} C]

/-- **2.1** A left `C`-module `G` is **flat** if `I ⊗_C G → Hom(-, X) ⊗_C G` is a monomorphism for
every object `X` and every finitely generated subfunctor `I ⊆ Hom(-, X)` ([OR, Thm. 3.2 (3)]; for
rings, finitely generated right ideals, [Lam-LMR, (4.12)]). By Yoneda (0.3) the target is `G(X)`.

This is flatness as a module (ambient flatness). It is not flatness as an object of the full
subcategory of flat modules, which asks every epimorphism there to be pure ([CI]). -/
class LeftModCat.Flat (G : LeftModCat.{v} C) : Prop where
  mono_tensor_yonedaSpan ⦃X : C⦄ ⦃n : ℕ⦄ ⦃Y : Fin n → C⦄ (β : ∀ j, Y j ⟶ X) :
    Mono (((ModCat.tensor ℤ).map (ModCat.yonedaSpan β).arrow).app G)

/-- **2.1** A right module is flat when it is flat as a left `Cᵒᵖ`-module (`ModCat C` is
`LeftModCat Cᵒᵖ`); by the swap (0.5) this says that `F ⊗_C -` passes the ideal test. -/
abbrev ModCat.Flat (F : ModCat.{v} C) : Prop :=
  LeftModCat.Flat (C := Cᵒᵖ) F

/-- **2.1** Flatness does not depend on `R`: the ideal test over any `R` (0.3, independence of
`R`). -/
theorem LeftModCat.flat_iff_mono_tensor (R : Type*) [CommRing R] [Linear R C]
    (G : LeftModCat.{v} C) :
    G.Flat ↔ ∀ ⦃X : C⦄ ⦃n : ℕ⦄ ⦃Y : Fin n → C⦄ (β : ∀ j, Y j ⟶ X),
      Mono (((ModCat.tensor R).map (ModCat.yonedaSpan β).arrow).app G) :=
  sorry

end FlatDef

/-- **2.1, rings** A left module `M` is flat if `I ⊗_A M → A ⊗_A M` is injective for every finitely
generated right ideal `I` ([Lam-LMR, (4.12)]). A right module `M` is flat when
`Module.BalancedFlat Aᵐᵒᵖ M`. If Mathlib generalizes `Module.Flat` to noncommutative rings, this
class is replaced by `Module.Flat`. -/
class Module.BalancedFlat (A : Type u) (M : Type v) [Ring A] [AddCommGroup M] [Module A M] :
    Prop where
  out ⦃I : Submodule Aᵐᵒᵖ A⦄ : I.FG →
    Function.Injective (BalancedTensorProduct.rTensor ℤ M I.subtype)

/-- **2.1, rings** Ring flatness is flatness over `SingleObj A` (0.2). -/
theorem Module.balancedFlat_iff_flat_singleObj (A : Type u) [Ring A] (M : Type u) [AddCommGroup M]
    [Module A M] :
    Module.BalancedFlat A M ↔
      LeftModCat.Flat ((moduleCatEquivLeftModCat.{u} A).functor.obj (ModuleCat.of A M)) :=
  sorry

/-- **2.1, commutative rings**: over a commutative ring, `BalancedFlat` is Mathlib's
`Module.Flat`. -/
theorem Module.balancedFlat_iff_flat {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M]
    [Module R M] : Module.BalancedFlat R M ↔ Module.Flat R M :=
  sorry

/-! ### 2.2 Tests -/

section Baer

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- **2.2** Baer's condition in `Mod C`: every map from a subfunctor of a representable extends to
the representable. -/
def ModCat.Baer (E : ModCat.{v} C) : Prop :=
  ∀ (X : C) (I : Subobject ((ModCat.yoneda C).obj X)) (φ : (I : ModCat.{v} C) ⟶ E),
    ∃ ψ : (ModCat.yoneda C).obj X ⟶ E, I.arrow ≫ ψ = φ

/-- **2.2, Baer's criterion** in `Mod C`: Zorn's lemma over partial extensions, with the
representables as generators (the argument of Mathlib's `Module.Baer.injective`). -/
theorem ModCat.baer_iff_injective (E : ModCat.{v} C) : ModCat.Baer E ↔ Injective E :=
  sorry

end Baer

section FlatTests

open ModCat

variable {C : Type u} [Category.{v} C] [Preadditive C] [EssentiallySmall.{v} C]

/-- **2.2, tests for flatness** of a left module `G`: (1) the ideal test (definition); (2) all
subfunctors of representables; (3) `- ⊗_C G` preserves monomorphisms; (4) `Tor_1(-, G) = 0`;
(5) `Tor_1(Hom(-, X) ⧸ I, G) = 0` for finitely generated `I`; (6) Lambek: the dual `G^E` is
injective for every injective cogenerator `E` ([OR, Thm. 3.2 (1), (3)]; [St, Thm. 3]; [Lambek]).
Route: Lambek and Baer, as [Lam-LMR, (4.12)]. -/
theorem LeftModCat.flat_tfae (G : LeftModCat.{v} C) :
    List.TFAE
      [G.Flat,
        ∀ (X : C) (I : Subobject ((ModCat.yoneda C).obj X)),
          Mono (((tensor ℤ).map I.arrow).app G),
        ∀ ⦃F F' : ModCat.{v} C⦄ (i : F ⟶ F'), Mono i → Mono (((tensor ℤ).map i).app G),
        ∀ F : ModCat.{v} C, IsZero (((tor ℤ 1).obj F).obj G),
        ∀ ⦃X : C⦄ ⦃n : ℕ⦄ ⦃Y : Fin n → C⦄ (β : ∀ j, Y j ⟶ X),
          IsZero (((tor ℤ 1).obj (cokernel (ModCat.yonedaSpan β).arrow)).obj G),
        ∀ E : ModuleCat.{v} ℤ, Injective E → IsCoseparator E →
          Injective ((LeftModCat.dual ℤ E).obj (op G))] :=
  sorry

/-- **2.2, Lambek's criterion** for any `R` and any injective cogenerator `E` of `R`-modules: the
adjunction of 0.7 and 0.7's one-map criterion. -/
theorem LeftModCat.flat_iff_injective_dual (R : Type*) [CommRing R] [Linear R C]
    (E : ModuleCat.{v} R) [Injective E] (hE : IsCoseparator E) (G : LeftModCat.{v} C) :
    G.Flat ↔ Injective ((LeftModCat.dual R E).obj (op G)) :=
  sorry

/-- **2.2** Tensoring with a flat left module preserves monomorphisms, for any `R`. -/
theorem LeftModCat.Flat.mono_tensor_map_app (R : Type*) [CommRing R] [Linear R C]
    (G : LeftModCat.{v} C) [G.Flat] {F F' : ModCat.{v} C} (i : F ⟶ F') [Mono i] :
    Mono (((tensor R).map i).app G) :=
  sorry

/-- **2.2** Tensoring with a flat right module preserves monomorphisms (the swap, 0.5). -/
theorem ModCat.Flat.mono_tensor_obj_map (R : Type*) [CommRing R] [Linear R C]
    (F : ModCat.{v} C) [ModCat.Flat F] {G G' : LeftModCat.{v} C} (g : G ⟶ G') [Mono g] :
    Mono (((tensor R).obj F).map g) :=
  sorry

/-- **2.2** A flat module has no higher `Tor`: `Tor_1(-, G) = 0` gives `Tor_{n+1}(-, G) = 0` by
dimension shifting along `0 → K → P → F → 0` (1.2, 1.3). -/
theorem LeftModCat.Flat.isZero_tor_succ (R : Type*) [CommRing R] [Linear R C]
    (G : LeftModCat.{v} C) [G.Flat] (F : ModCat.{v} C) (n : ℕ) :
    IsZero (((tor R (n + 1)).obj F).obj G) :=
  sorry

/-- **2.2, `Tor` commutes with filtered colimits** in the left-module variable. Route: compute
`Tor` from a projective resolution `P` of `F` (1.3); `P_p ⊗_C -` preserves colimits (0.3), and
filtered colimits are exact in `ModuleCat R`. -/
instance ModCat.preservesFilteredColimits_tor_obj (R : Type*) [CommRing R] [Linear R C]
    (F : ModCat.{v} C) (n : ℕ) : PreservesFilteredColimitsOfSize.{v, v} ((tor R n).obj F) :=
  sorry

end FlatTests

section BalancedFlatTests

variable {A : Type u} [Ring A]

/-- **2.2, rings: tests for flatness**: the definition; all right ideals; all injections of right
modules; vanishing of `Tor_1`; vanishing of `Tor_1` on cyclic right modules with finitely generated
relations; Lambek's character-module test ([Lam-LMR, (4.9), (4.12)]; [Lambek, Theorem, p. 239]). -/
theorem Module.balancedFlat_tfae [Small.{v} A] (M : Type v) [AddCommGroup M] [Module A M] :
    List.TFAE
      [Module.BalancedFlat A M,
        ∀ I : Submodule Aᵐᵒᵖ A, Function.Injective (BalancedTensorProduct.rTensor ℤ M I.subtype),
        ∀ ⦃P Q : Type v⦄ [AddCommGroup P] [Module Aᵐᵒᵖ P] [AddCommGroup Q] [Module Aᵐᵒᵖ Q]
          (i : P →ₗ[Aᵐᵒᵖ] Q), Function.Injective i →
            Function.Injective (BalancedTensorProduct.rTensor ℤ M i),
        ∀ N : ModuleCat.{v} Aᵐᵒᵖ,
          IsZero (((BalancedTor.{v} ℤ A 1).obj N).obj (ModuleCat.of A M)),
        ∀ I : Submodule Aᵐᵒᵖ A, I.FG →
          IsZero (((BalancedTor.{v} ℤ A 1).obj (ModuleCat.of Aᵐᵒᵖ (Shrink.{v} (A ⧸ I)))).obj
            (ModuleCat.of A M)),
        Module.Injective Aᵐᵒᵖ (CharacterModule M)] :=
  sorry

/-- **2.2, rings** Flat modules have no higher `Tor`. -/
theorem isZero_balancedTor_succ_of_balancedFlat [Small.{v} A] (N : ModuleCat.{v} Aᵐᵒᵖ)
    (M : ModuleCat.{v} A) [Module.BalancedFlat A M] (n : ℕ) :
    IsZero (((BalancedTor ℤ A (n + 1)).obj N).obj M) :=
  sorry

/-- **2.2, rings** Ring `Tor` commutes with filtered colimits in the left-module variable. -/
instance preservesFilteredColimits_balancedTor_obj (R : Type t) [CommRing R] [Algebra R A]
    [Small.{v} A] (M : ModuleCat.{v} Aᵐᵒᵖ) (n : ℕ) :
    PreservesFilteredColimitsOfSize.{v, v} ((BalancedTor R A n).obj M) :=
  sorry

end BalancedFlatTests

/-! ### 2.3 The Lazard block -/

section Lazard

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- **2.3** A relation `∑_j G(β_j)(y_j) = 0` in `G(X)` is **trivial** if there are finitely many
`z_i ∈ G(Z_i)` and maps `α_ij : Z_i ⟶ Y_j` with `y_j = ∑_i G(α_ij)(z_i)` and `∑_j α_ij ≫ β_j = 0`
for all `i` ([OR, Thm. 3.2 (4)], mirrored to left modules); the shape of Mathlib's
`Module.Flat.IsTrivialRelation`. -/
def LeftModCat.IsTrivialRelation (G : LeftModCat.{v} C) {X : C} {n : ℕ} {Y : Fin n → C}
    (β : ∀ j, Y j ⟶ X) (y : ∀ j, G.obj.obj (Y j)) : Prop :=
  ∃ (m : ℕ) (Z : Fin m → C) (z : ∀ i, G.obj.obj (Z i)) (α : ∀ i j, Z i ⟶ Y j),
    (∀ j, y j = ∑ i, (G.obj.map (α i j)).hom (z i)) ∧ ∀ i, ∑ j, α i j ≫ β j = 0

variable (C) in
/-- **2.3** Finite sums of representables `Hom(Z₁, -) ⊕ ⋯ ⊕ Hom(Zₘ, -)`, the finitely generated
free left modules. -/
def LeftModCat.isFiniteFree : ObjectProperty (LeftModCat.{v} C) := fun P ↦
  ∃ (m : ℕ) (Z : Fin m → C), Nonempty (P ≅ ∐ fun i ↦ (LeftModCat.coyoneda C).obj (op (Z i)))

/-- **2.3** The category of maps to `G` from finite sums of representables; the shape of Tau
Ceti's `TauCeti.FiniteFreeOver`. -/
abbrev LeftModCat.FiniteFreeOver (G : LeftModCat.{v} C) :=
  CostructuredArrow (LeftModCat.isFiniteFree C).ι G

/-- **2.3** An epimorphism `p : L ⟶ M` is **pure** if every map from a finitely presented module
to `M` lifts along `p` ([St, §2]). -/
def LeftModCat.IsPureEpi {L M : LeftModCat.{v} C} (p : L ⟶ M) : Prop :=
  Epi p ∧ ∀ ⦃P : LeftModCat.{v} C⦄ [IsFinitelyPresentable.{v} P] (φ : P ⟶ M),
    ∃ ψ : P ⟶ L, ψ ≫ p = φ

/-- **2.3** A module is **pure-projective** if it is projective with respect to pure
epimorphisms. -/
def LeftModCat.IsPureProjective (M : LeftModCat.{v} C) : Prop :=
  ∀ ⦃L L' : LeftModCat.{v} C⦄ (p : L ⟶ L'), LeftModCat.IsPureEpi p →
    ∀ φ : M ⟶ L', ∃ ψ : M ⟶ L, ψ ≫ p = φ

variable [EssentiallySmall.{v} C]

/-- **2.3, equational criterion** ([OR, Thm. 3.2 (4)]; rings: [Lam-LMR, (4.24)]). -/
theorem LeftModCat.flat_iff_forall_isTrivialRelation (G : LeftModCat.{v} C) :
    G.Flat ↔ ∀ ⦃X : C⦄ ⦃n : ℕ⦄ ⦃Y : Fin n → C⦄ (β : ∀ j, Y j ⟶ X) (y : ∀ j, G.obj.obj (Y j)),
      ∑ j, (G.obj.map (β j)).hom (y j) = 0 → G.IsTrivialRelation β y :=
  sorry

/-- **2.3, factorization**: `G` is flat exactly when every map from a finitely presented module to
`G` factors through a finite sum of representables ([Lazard, Lemme 1.1, Thm. 1.2]; [St, Lemma 8];
[CB, §1.3]). -/
theorem LeftModCat.flat_iff_forall_exists_factorization (G : LeftModCat.{v} C) :
    G.Flat ↔ ∀ ⦃P : LeftModCat.{v} C⦄ [IsFinitelyPresentable.{v} P] (φ : P ⟶ G),
      ∃ (Q : LeftModCat.{v} C) (a : P ⟶ Q) (b : Q ⟶ G), LeftModCat.isFiniteFree C Q ∧ a ≫ b = φ :=
  sorry

/-- **2.3, filtered category of elements**: `G` is flat exactly when the maps to `G` from finite
sums of representables form a filtered category ([OR, Thm. 3.2 (6)]; [CB, §1.3]). -/
theorem LeftModCat.flat_iff_isFiltered_finiteFreeOver (G : LeftModCat.{v} C) :
    G.Flat ↔ IsFiltered G.FiniteFreeOver :=
  sorry

/-- **2.3, Lazard–Govorov**: `G` is flat exactly when it is a filtered colimit of finite sums of
representables ([OR, Thm. 3.2 (5)]; [Mitchell, Thm. 10.1b, p. 48]; [CB, §1.3]; [Lazard, Thm. 1.2];
[Govorov]). The converse direction uses 2.2's `Tor` and filtered colimits. -/
theorem LeftModCat.flat_iff_exists_isColimit (G : LeftModCat.{v} C) :
    G.Flat ↔ ∃ (J : Type v) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ LeftModCat.{v} C)
      (c : Cocone D), Nonempty (IsColimit c) ∧ (∀ j, LeftModCat.isFiniteFree C (D.obj j)) ∧
        Nonempty (c.pt ≅ G) :=
  sorry

/-- **2.3, purity**: `G` is flat exactly when every epimorphism onto `G` is pure ([St, Thm. 3];
[Lazard, Cor. 1.3]). -/
theorem LeftModCat.flat_iff_forall_isPureEpi (G : LeftModCat.{v} C) :
    G.Flat ↔ ∀ ⦃L : LeftModCat.{v} C⦄ (p : L ⟶ G), Epi p → LeftModCat.IsPureEpi p :=
  sorry

/-- **2.3** A finitely presented flat module is projective. Route: 1.4 (over `Cᵒᵖ`, with the
balance) gives `stable End(G) ≅ Tor_1(Tr G, G) = 0`, so the identity of `G` factors through a
projective. Alternatively the identity factors through a finite sum of representables
([St, Lemma 7 (ii)]; [Lazard, Cor. 1.4]). -/
theorem LeftModCat.Flat.projective_of_isFinitelyPresentable (G : LeftModCat.{v} C) [G.Flat]
    [IsFinitelyPresentable.{v} G] : Projective G :=
  sorry

/-- **2.3** A flat pure-projective module is projective: an epimorphism from a projective onto it
is pure, hence splits. -/
theorem LeftModCat.Flat.projective_of_isPureProjective (G : LeftModCat.{v} C) [G.Flat]
    (hG : G.IsPureProjective) : Projective G :=
  sorry

/-- **2.3, additive categories**: with finite biproducts, single representables suffice
([CB, §1.3]; [OR, Cor. 3.3]). -/
theorem LeftModCat.flat_iff_isFiltered_costructuredArrow_coyoneda [HasFiniteBiproducts C]
    (G : LeftModCat.{v} C) : G.Flat ↔ IsFiltered (CostructuredArrow (LeftModCat.coyoneda C) G) :=
  sorry

/-- **2.3, bridge to Mathlib's ind-objects**: over an additive `C`, a right module is flat exactly
when its underlying presheaf of sets is an ind-object ([Krause-Smashing, §2.3, p. 115]). -/
theorem ModCat.flat_iff_isIndObject [HasFiniteBiproducts C] (F : ModCat.{v} C) :
    ModCat.Flat F ↔ IsIndObject (F.obj ⋙ forget AddCommGrpCat.{v}) :=
  sorry

/-- **2.3, bridge to Mathlib's type-valued flat functors**: over an additive `C`, a left module is
flat exactly when its category of elements is cofiltered (`Functor.isCofiltered_elements`). -/
theorem LeftModCat.flat_iff_isCofiltered_elements [HasFiniteBiproducts C] (G : LeftModCat.{v} C) :
    G.Flat ↔ IsCofiltered (G.obj ⋙ forget AddCommGrpCat.{v}).Elements :=
  sorry

end Lazard

section BalancedFlatLazard

variable {A : Type u} [Ring A]

/-- **2.3, rings: Lazard** `M` is flat exactly when the finite free modules over `M` (Tau Ceti's
`FiniteFreeOver`) form a filtered category. -/
theorem Module.balancedFlat_iff_isFiltered_finiteFreeOver (M : Type u) [AddCommGroup M]
    [Module A M] : Module.BalancedFlat A M ↔ IsFiltered (TauCeti.FiniteFreeOver A M) :=
  sorry

/-- **2.3, rings** A flat module is the filtered colimit of the finite free modules over it. For a
commutative ring this is Tau Ceti's `TauCeti.flatModuleFilteredFree`, which becomes a
corollary. -/
noncomputable def Module.BalancedFlat.denseAt (M : Type u) [AddCommGroup M] [Module A M]
    [Module.BalancedFlat A M] :
    (TauCeti.finiteFreeModuleInclusion A).DenseAt (ModuleCat.of A M) :=
  sorry

/-- **2.3, rings** Every map from a finitely presented module to a flat module factors through a
finite free module (Mathlib's `Module.Flat.exists_factorization_of_finitePresentation` for
commutative rings). -/
theorem Module.BalancedFlat.exists_factorization_of_finitePresentation {M : Type v}
    [AddCommGroup M] [Module A M] [Module.BalancedFlat A M] {P : Type*} [AddCommGroup P]
    [Module A P] [Module.FinitePresentation A P] (h₁ : P →ₗ[A] M) :
    ∃ (k : ℕ) (h₂ : P →ₗ[A] (Fin k →₀ A)) (h₃ : (Fin k →₀ A) →ₗ[A] M), h₁ = h₃ ∘ₗ h₂ :=
  sorry

/-- **2.3, rings** A finitely presented flat module is projective: by 1.4,
`stable End(M) ≅ Tor_1^A(Tr M, M) = 0`. -/
theorem Module.BalancedFlat.projective_of_finitePresentation {M : Type v} [AddCommGroup M]
    [Module A M] [Module.FinitePresentation A M] [Module.BalancedFlat A M] :
    Module.Projective A M :=
  sorry

end BalancedFlatLazard

/-! ### 2.4 Left exact functors, triangulated categories and the representation theorem -/

section LeftExact

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- **2.4** `g` is a **weak cokernel** of `f`: `f ≫ g = 0`, and every `h` with `f ≫ h = 0` factors
through `g`, not necessarily uniquely. -/
def IsWeakCokernel {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : Prop :=
  f ≫ g = 0 ∧ ∀ ⦃W : C⦄ (h : Y ⟶ W), f ≫ h = 0 → ∃ k : Z ⟶ W, g ≫ k = h

variable [EssentiallySmall.{v} C]

/-- **2.4, weak cokernels**: over an additive `C` with weak cokernels, a right module is flat
exactly when it turns weak cokernels into exact sequences ([CB, §1.2, Lemma 2, and §1.3]). -/
theorem ModCat.flat_iff_exact_of_isWeakCokernel [HasFiniteBiproducts C]
    (hC : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), ∃ (Z : C) (g : Y ⟶ Z), IsWeakCokernel f g)
    (F : ModCat.{v} C) :
    ModCat.Flat F ↔ ∀ ⦃X Y Z : C⦄ (f : X ⟶ Y) (g : Y ⟶ Z), IsWeakCokernel f g →
      Function.Exact (F.obj.map g.op).hom (F.obj.map f.op).hom :=
  sorry

/-- **2.4, flat = left exact**: over an additive `C` with cokernels, a right module is flat exactly
when it is left exact ([Fisher, Thms. 1.3–1.4] for abelian `C`; [OR, Cor. 3.4]; [CB, §2.2];
[Simson, Thm. 2.1 (b)]). -/
theorem ModCat.flat_iff_preservesFiniteLimits [HasFiniteBiproducts C] [HasCokernels C]
    (F : ModCat.{v} C) : ModCat.Flat F ↔ PreservesFiniteLimits F.obj :=
  sorry

end LeftExact

section Triangulated

open Pretriangulated.Opposite

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [EssentiallySmall.{v} C]

/-- **2.4, triangulated categories**: over a skeletally small triangulated `C`, a right module is
flat exactly when it is cohomological, that is, homological on `Cᵒᵖ` ([Krause-Smashing, Lemma 2.7];
[Beligiannis, Rem. 8.12]). -/
theorem ModCat.flat_iff_isHomological (F : ModCat.{v} C) : ModCat.Flat F ↔ F.obj.IsHomological :=
  sorry

end Triangulated

section Representation

variable (C : Type u) [Category.{v} C] [Preadditive C] [EssentiallySmall.{v} C]

/-- **2.4** The flat right modules, as a property of objects of `Mod C`. -/
abbrev ModCat.flat : ObjectProperty (ModCat.{v} C) := fun F ↦ ModCat.Flat F

/-- **2.4** For a small additive `C`, the flat right modules form a finitely accessible
category ([CB, §1.4]). -/
instance [HasFiniteBiproducts C] :
    IsFinitelyAccessibleCategory.{v} (ModCat.flat C).FullSubcategory :=
  sorry

variable {C} in
/-- **2.4** For a small additive `C`, the finitely presented flat right modules are the retracts of
representables ([CB, §1.4 (1)]). -/
theorem ModCat.isFinitelyPresentable_flat_iff [HasFiniteBiproducts C]
    (F : (ModCat.flat C).FullSubcategory) :
    IsFinitelyPresentable.{v} F ↔ ∃ X : C, Nonempty (Retract F.obj ((ModCat.yoneda C).obj X)) :=
  sorry

variable (𝒜 : Type u) [Category.{v} 𝒜] [Preadditive 𝒜] [HasFiniteBiproducts 𝒜]
  [IsFinitelyAccessibleCategory.{v} 𝒜]

/-- **2.4** The finitely presented objects `fp(𝒜)` of `𝒜`. -/
abbrev FinitelyPresented : Type _ := (ObjectProperty.isFinitelyPresentable.{v} 𝒜).FullSubcategory

/-- **2.4, Crawley-Boevey's representation theorem**: a finitely accessible additive category
`𝒜` is equivalent, through the restricted Yoneda functor `X ↦ Hom(-, X)` on `fp(𝒜)`, to the flat
right modules over `fp(𝒜)` ([CB, §1.4]). Mathlib's `IsFinitelyAccessibleCategory`, not
`IsLocallyFinitelyPresentable`: no cocompleteness is assumed. -/
noncomputable def restrictedYonedaEquivFlat :
    𝒜 ≌ (ModCat.flat (FinitelyPresented 𝒜)).FullSubcategory :=
  sorry

end Representation

/-! ### 2.5 Bass's flat module -/

section Bass

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- **2.5** An inverse system `F : ℕᵒᵖ ⥤ C` is **factorizable** if for every `i` there is `j ≥ i`
such that the map `F j → F i` factors through every later map `F k → F i`, `k ≥ j`
([Simson, Def. 3.1, p. 99]). For a chain `c₀ ← c₁ ← ⋯` over a ring, at `i = 0` this says that
the chain `a₀A ⊇ a₀a₁A ⊇ ⋯` of principal right ideals stabilizes. -/
def IsFactorizable (F : ℕᵒᵖ ⥤ C) : Prop :=
  ∀ i : ℕ, ∃ (j : ℕ) (hij : i ≤ j), ∀ (k : ℕ) (hjk : j ≤ k),
    ∃ t : F.obj (op j) ⟶ F.obj (op k),
      t ≫ F.map (homOfLE (hij.trans hjk)).op = F.map (homOfLE hij).op

variable (c : ℕ → C) (f : ∀ i, c (i + 1) ⟶ c i)

/-- **2.5** The sequence `Hom(c₀, -) → Hom(c₁, -) → ⋯` of a chain `c₀ ← c₁ ← ⋯`, with maps
`Hom(f_i, -)`. -/
noncomputable def LeftModCat.bassDiagram : ℕ ⥤ LeftModCat.{v} C :=
  Functor.ofSequence fun i ↦ (LeftModCat.coyoneda C).map (f i).op

/-- **2.5, Bass's flat module** of a chain: `B = colim Hom(c_i, -)`. For `C = SingleObj A` this is
Bass's module ([Bass, Lemma 1.1]; [Harada, Remark 1]). -/
noncomputable def LeftModCat.bassModule : LeftModCat.{v} C :=
  colimit (LeftModCat.bassDiagram c f)

/-- **2.5** Bass's module is zero exactly when every tail of the chain has a zero composite: for
every `i` some `c_j → c_i`, `j ≥ i`, vanishes. Used for T-nilpotence (4.1). -/
theorem LeftModCat.isZero_bassModule_iff :
    IsZero (LeftModCat.bassModule c f) ↔
      ∀ i : ℕ, ∃ (j : ℕ) (hij : i ≤ j), (Functor.ofOpSequence f).map (homOfLE hij).op = 0 :=
  sorry

/-- **2.5** The telescope map `e_i ↦ e_i - Hom(f_i, -) e_{i+1}` on `⊕_i Hom(c_i, -)`. -/
noncomputable def LeftModCat.bassTelescope :
    (∐ fun i ↦ (LeftModCat.coyoneda C).obj (op (c i))) ⟶
      ∐ fun i ↦ (LeftModCat.coyoneda C).obj (op (c i)) :=
  Limits.Sigma.desc fun i ↦ Limits.Sigma.ι (fun i ↦ (LeftModCat.coyoneda C).obj (op (c i))) i -
    (LeftModCat.coyoneda C).map (f i).op ≫
      Limits.Sigma.ι (fun i ↦ (LeftModCat.coyoneda C).obj (op (c i))) (i + 1)

/-- **2.5** The map `⊕_i Hom(c_i, -) → B`. -/
noncomputable def LeftModCat.bassπ :
    (∐ fun i ↦ (LeftModCat.coyoneda C).obj (op (c i))) ⟶ LeftModCat.bassModule c f :=
  Limits.Sigma.desc fun i ↦ colimit.ι (LeftModCat.bassDiagram c f) i

theorem LeftModCat.bassTelescope_comp_bassπ :
    LeftModCat.bassTelescope c f ≫ LeftModCat.bassπ c f = 0 :=
  sorry

/-- **2.5, telescope presentation** `0 → ⊕ Hom(c_i, -) → ⊕ Hom(c_i, -) → B → 0`; so `B` has
projective dimension at most one. -/
theorem LeftModCat.bassTelescope_shortExact :
    (ShortComplex.mk _ _ (LeftModCat.bassTelescope_comp_bassπ c f)).ShortExact :=
  sorry

/-- **2.5** Bass's module is flat (2.3). -/
instance [EssentiallySmall.{v} C] : (LeftModCat.bassModule c f).Flat :=
  sorry

/-- **2.5** If Bass's module is projective, the chain is factorizable: an adaptation of
[Bass, Lemma 1.3], with [Harada, Remark 1] for rings with enough idempotents. -/
theorem LeftModCat.isFactorizable_of_projective_bassModule
    [Projective (LeftModCat.bassModule c f)] : IsFactorizable (Functor.ofOpSequence f) :=
  sorry

end Bass

section BalancedBass

variable {A : Type u} [Ring A]

variable (A) in
/-- **2.5, rings** The relations of Bass's flat module: the span of the `eᵢ - aᵢ • eᵢ₊₁` in
`ℕ →₀ A`. -/
noncomputable def bassRelations (a : ℕ → A) : Submodule A (ℕ →₀ A) :=
  Submodule.span A (Set.range fun i ↦ Finsupp.single i 1 - Finsupp.single (i + 1) (a i))

/-- **2.5, rings** Bass's flat module is flat. -/
theorem balancedFlat_bassRelations (a : ℕ → A) :
    Module.BalancedFlat A ((ℕ →₀ A) ⧸ bassRelations A a) :=
  sorry

/-- **2.5, rings** If Bass's module is projective, the chain of principal right ideals
`a₀A ⊇ a₀a₁A ⊇ a₀a₁a₂A ⊇ ⋯` is eventually constant ([Bass, Lemmas 1.1–1.3]). -/
theorem exists_span_prod_eq_of_projective_bassRelations (a : ℕ → A)
    [Module.Projective A ((ℕ →₀ A) ⧸ bassRelations A a)] :
    ∃ n, ∀ m ≥ n, Submodule.span Aᵐᵒᵖ {(List.ofFn fun i : Fin m ↦ a i).prod} =
      Submodule.span Aᵐᵒᵖ {(List.ofFn fun i : Fin n ↦ a i).prod} :=
  sorry

end BalancedBass

/-! ### 2.6 Closure properties -/

section FlatClosure

variable {C : Type u} [Category.{v} C] [Preadditive C] [EssentiallySmall.{v} C]

/-- **2.6** Projective modules are flat (0.4). -/
instance LeftModCat.Flat.of_projective (G : LeftModCat.{v} C) [Projective G] : G.Flat :=
  sorry

/-- **2.6** Flatness passes to retracts. -/
theorem LeftModCat.Flat.of_retract {G G' : LeftModCat.{v} C} (r : Retract G' G) [G.Flat] :
    G'.Flat :=
  sorry

/-- **2.6** A direct sum is flat exactly when every summand is. -/
theorem LeftModCat.flat_sigma_iff {ι : Type v} (G : ι → LeftModCat.{v} C) :
    (∐ G).Flat ↔ ∀ i, (G i).Flat :=
  sorry

/-- **2.6** In a short exact sequence with flat third term, the middle term is flat exactly when
the first is ([Mitchell, Cor. 10.4b, p. 49]). -/
theorem LeftModCat.flat_iff_of_shortExact {S : ShortComplex (LeftModCat.{v} C)}
    (hS : S.ShortExact) [S.X₃.Flat] : S.X₂.Flat ↔ S.X₁.Flat :=
  sorry

/-- **2.6** A filtered colimit of flat modules is flat (2.2: `Tor` commutes with filtered
colimits). -/
theorem LeftModCat.Flat.of_isColimit {J : Type v} [SmallCategory J] [IsFiltered J]
    {D : J ⥤ LeftModCat.{v} C} {c : Cocone D} (hc : IsColimit c) (h : ∀ j, (D.obj j).Flat) :
    c.pt.Flat :=
  sorry

/-- **2.6, flat quotients**: for `0 → K → F → M → 0` with `F` flat, `M` is flat exactly when
`N ⊗_C K → N ⊗_C F` is a monomorphism for every right module `N` ([Lam-FC, (24.23)]). -/
theorem LeftModCat.flat_iff_mono_tensor_of_shortExact {S : ShortComplex (LeftModCat.{v} C)}
    (hS : S.ShortExact) [S.X₂.Flat] :
    S.X₃.Flat ↔ ∀ N : ModCat.{v} C, Mono (((ModCat.tensor ℤ).obj N).map S.f) :=
  sorry

end FlatClosure

section BalancedFlatClosure

variable {A : Type u} [Ring A]
  {M M₁ M₂ M₃ : Type v} [AddCommGroup M] [Module A M] [AddCommGroup M₁] [Module A M₁]
  [AddCommGroup M₂] [Module A M₂] [AddCommGroup M₃] [Module A M₃]

/-- **2.6, rings** Projective modules are flat (an instance in Tau Ceti). -/
theorem Module.BalancedFlat.of_projective [Module.Projective A M] : Module.BalancedFlat A M :=
  sorry

/-- **2.6, rings** Flatness is invariant under linear equivalence. -/
theorem Module.BalancedFlat.of_linearEquiv (e : M₁ ≃ₗ[A] M₂) [Module.BalancedFlat A M₁] :
    Module.BalancedFlat A M₂ :=
  sorry

/-- **2.6, rings** A direct sum is flat exactly when every summand is. -/
theorem Module.balancedFlat_directSum_iff {ι : Type v} (N : ι → Type v)
    [∀ i, AddCommGroup (N i)] [∀ i, Module A (N i)] :
    Module.BalancedFlat A (⨁ i, N i) ↔ ∀ i, Module.BalancedFlat A (N i) :=
  sorry

/-- **2.6, rings** In a short exact sequence with flat third term, the middle term is flat exactly
when the first is ([Lam-LMR, (4.13)]). -/
theorem Module.balancedFlat_iff_of_exact {f : M₁ →ₗ[A] M₂} {g : M₂ →ₗ[A] M₃}
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    [Module.BalancedFlat A M₃] : Module.BalancedFlat A M₂ ↔ Module.BalancedFlat A M₁ :=
  sorry

/-- **2.6, rings: flat quotients**: if `F` and `F ⧸ K` are flat, then `K ∩ IF = IK` for every
two-sided ideal `I` ([Lam-LMR, (4.14)]). -/
theorem Submodule.inf_smul_eq_smul_of_balancedFlat {F : Type v} [AddCommGroup F] [Module A F]
    [Module.BalancedFlat A F] (K : Submodule A F) [Module.BalancedFlat A (F ⧸ K)] (I : Ideal A)
    [I.IsTwoSided] : K ⊓ I • (⊤ : Submodule A F) = I • K :=
  sorry

end BalancedFlatClosure

/-- **Layer 2 check** `ℤ ⧸ n` is not flat for `n ≥ 2`. -/
theorem not_balancedFlat_zmod (n : ℕ) (hn : 2 ≤ n) : ¬ Module.BalancedFlat ℤ (ZMod n) :=
  sorry

/-! ## Layer 3: flat dimension, global and weak global dimension, and Auslander's theorem

Dimensions are category-primary. The flat dimension of a left `C`-module `G` is defined by the
vanishing of `Tor_i(Hom(-, X) ⧸ I, G)` for the finitely presented cyclic right modules, the shape
of Mathlib's `projectiveDimension`; flat dimension `≤ 0` is Layer 2's ideal test. The global
dimension is defined for any abelian category, and Tau Ceti's ring `TauCeti.globalDimension` is the
case `ModuleCat A`. The weak global dimension of `C` is the supremum of the flat dimensions of the
left modules; it is left-right symmetric. Auslander's theorem says that it equals the global
dimension of the left modules when every representable `Hom(X, -)` is a Noetherian object. Rings
keep native definitions with bridges to `SingleObj A`. `Tor` is taken with `R = ℤ`: dimensions do
not depend on `R` (1.6). -/

/-! ### 3.1 Flat dimension -/

section FlatDimension

open ModCat

variable {C : Type u} [Category.{v} C] [Preadditive C] [EssentiallySmall.{v} C]

/-- **3.1** `G` has flat dimension `< n`: `Tor_i(Hom(-, X) ⧸ I, G) = 0` for every `i ≥ n`, every
object `X` and every finitely generated subfunctor `I ⊆ Hom(-, X)`. Universe-free: it quantifies
over objects and finite families of morphisms of `C`. The shape of Mathlib's
`HasProjectiveDimensionLT`; flat dimension `< 1` is flatness (2.2 (5)). -/
class LeftModCat.HasFlatDimensionLT (G : LeftModCat.{v} C) (n : ℕ) : Prop where
  isZero_tor ⦃i : ℕ⦄ (hi : n ≤ i) ⦃X : C⦄ ⦃m : ℕ⦄ ⦃Y : Fin m → C⦄ (β : ∀ j, Y j ⟶ X) :
    IsZero (((tor ℤ i).obj (cokernel (ModCat.yonedaSpan β).arrow)).obj G)

/-- **3.1** `G` has flat dimension `≤ n`. -/
abbrev LeftModCat.HasFlatDimensionLE (G : LeftModCat.{v} C) (n : ℕ) : Prop :=
  G.HasFlatDimensionLT (n + 1)

theorem LeftModCat.HasFlatDimensionLT.of_le {G : LeftModCat.{v} C} {n m : ℕ}
    (h : G.HasFlatDimensionLT n) (hnm : n ≤ m) : G.HasFlatDimensionLT m :=
  ⟨fun _ hi _ _ _ β ↦ h.isZero_tor (hnm.trans hi) β⟩

/-- **3.1** The flat dimension, in `WithBot ℕ∞`, `⊥` exactly for the zero module. The shape of
Mathlib's `projectiveDimension`. -/
noncomputable def LeftModCat.flatDimension (G : LeftModCat.{v} C) : WithBot ℕ∞ :=
  sInf {d : WithBot ℕ∞ | ∀ i : ℕ, d < i → G.HasFlatDimensionLT i}

/-- **3.1** Right modules: flat dimension as left `Cᵒᵖ`-modules (`ModCat C` is `LeftModCat Cᵒᵖ`). -/
abbrev ModCat.HasFlatDimensionLT (F : ModCat.{v} C) (n : ℕ) : Prop :=
  LeftModCat.HasFlatDimensionLT (C := Cᵒᵖ) F n

/-- **3.1** A right module has flat dimension `≤ n`. -/
abbrev ModCat.HasFlatDimensionLE (F : ModCat.{v} C) (n : ℕ) : Prop :=
  ModCat.HasFlatDimensionLT F (n + 1)

/-- **3.1** The flat dimension of a right module. -/
noncomputable abbrev ModCat.flatDimension (F : ModCat.{v} C) : WithBot ℕ∞ :=
  LeftModCat.flatDimension (C := Cᵒᵖ) F

theorem LeftModCat.flatDimension_le_iff (G : LeftModCat.{v} C) (n : ℕ) :
    G.flatDimension ≤ n ↔ G.HasFlatDimensionLE n :=
  sorry

theorem LeftModCat.flatDimension_eq_bot_iff (G : LeftModCat.{v} C) :
    G.flatDimension = ⊥ ↔ IsZero G :=
  sorry

/-- **3.1** Flat dimension `≤ 0` is flatness: the definition at `n = 0` is 2.2 (5). -/
theorem LeftModCat.hasFlatDimensionLE_zero_iff (G : LeftModCat.{v} C) :
    G.HasFlatDimensionLE 0 ↔ G.Flat :=
  sorry

/-- **3.1, the classical definition**: for `n : ℕ`, the following are equivalent: (1) flat
dimension `≤ n`; (2) `Tor_i(-, G) = 0` for all `i > n`; (3) `Tor_{n+1}(-, G) = 0`; (4) `G` has a
flat resolution of length `≤ n`; (5) the `n`-th syzygy of every projective resolution is flat;
(6) the `n`-th syzygy of some projective resolution is flat. The `n`-th syzygy of a projective
resolution `P` is `P.complex.opcycles n = coker (P_{n+1} → P_n)`; for `n = 0` it is `G`. Route:
dimension shifting in either variable (1.2, 1.3); (1) ⇒ (5) is 2.2 (5) applied to the `n`-th
syzygy `K`, since `Tor_1(-, K) ≅ Tor_{n+1}(-, G)`. (2) holds for right modules in every universe;
in Lean it is stated in the universe `v`. -/
theorem LeftModCat.hasFlatDimensionLE_tfae (G : LeftModCat.{v} C) (n : ℕ) :
    List.TFAE
      [G.HasFlatDimensionLE n,
        ∀ (F : ModCat.{v} C) (i : ℕ), n < i → IsZero (((tor ℤ i).obj F).obj G),
        ∀ F : ModCat.{v} C, IsZero (((tor ℤ (n + 1)).obj F).obj G),
        ∃ (K : ChainComplex (LeftModCat.{v} C) ℕ) (π : K ⟶ (ChainComplex.single₀ _).obj G),
          QuasiIso π ∧ (∀ i, LeftModCat.Flat (K.X i)) ∧ ∀ i, n < i → IsZero (K.X i),
        ∀ P : ProjectiveResolution G, LeftModCat.Flat (P.complex.opcycles n),
        ∃ P : ProjectiveResolution G, LeftModCat.Flat (P.complex.opcycles n)] :=
  sorry

/-- **3.1** Flat dimension is at most projective dimension (2.6: projective modules are flat). -/
theorem LeftModCat.flatDimension_le_projectiveDimension (G : LeftModCat.{v} C) :
    G.flatDimension ≤ projectiveDimension G :=
  sorry

/-- **3.1, dimension shifting** along `0 → K → F → M → 0` with `F` flat. -/
theorem LeftModCat.hasFlatDimensionLE_succ_iff {S : ShortComplex (LeftModCat.{v} C)}
    (hS : S.ShortExact) [S.X₂.Flat] (n : ℕ) :
    S.X₃.HasFlatDimensionLE (n + 1) ↔ S.X₁.HasFlatDimensionLE n :=
  sorry

/-- **3.1** `Tor` is computed by flat resolutions: for a flat resolution `K → G`,
`Tor_n(F, G) ≅ H_n(F ⊗_C K)`. Route: the balance (1.3) computes both sides from a projective
resolution of `F`, and `- ⊗_C K_q` is exact (2.2). -/
noncomputable def ModCat.torObjIsoHomologyOfFlat (F : ModCat.{v} C) {G : LeftModCat.{v} C}
    (K : ChainComplex (LeftModCat.{v} C) ℕ) (π : K ⟶ (ChainComplex.single₀ _).obj G)
    [QuasiIso π] (hK : ∀ i, LeftModCat.Flat (K.X i)) (n : ℕ) :
    ((tor ℤ n).obj F).obj G ≅
      (HomologicalComplex.homologyFunctor _ _ n).obj
        ((((tensor ℤ).obj F).mapHomologicalComplex _).obj K) :=
  sorry

/-- **3.1, duality**: for an injective cogenerator `E` of `R`-modules, the flat dimension of `G` is
the injective dimension of its dual `G^E` (Layer 1's `Tor`–`Ext` duality; [Lam-LMR, (5.57)] for
rings and `E = ℚ ⧸ ℤ`). -/
theorem LeftModCat.flatDimension_eq_injectiveDimension_dual (R : Type*) [CommRing R]
    [Linear R C] (E : ModuleCat.{v} R) [Injective E] (hE : IsCoseparator E)
    (G : LeftModCat.{v} C) :
    G.flatDimension = injectiveDimension ((LeftModCat.dual R E).obj (op G)) :=
  sorry

end FlatDimension

section RingFlatDimension

variable {A : Type u} [Ring A] [Small.{v} A]

/-- **3.1, rings** `M` has flat dimension `< n`: `Tor_i^A(A ⧸ I, M) = 0` for every `i ≥ n` and
every finitely generated right ideal `I`. Native (Convention 5); the shape of Mathlib's
`HasProjectiveDimensionLT`. -/
class HasFlatDimensionLT (M : ModuleCat.{v} A) (n : ℕ) : Prop where
  isZero ⦃i : ℕ⦄ (hi : n ≤ i) ⦃I : Submodule Aᵐᵒᵖ A⦄ (hI : I.FG) :
    IsZero (((BalancedTor.{v} ℤ A i).obj (ModuleCat.of Aᵐᵒᵖ (Shrink.{v} (A ⧸ I)))).obj M)

/-- **3.1, rings** `M` has flat dimension `≤ n`. -/
abbrev HasFlatDimensionLE (M : ModuleCat.{v} A) (n : ℕ) : Prop :=
  HasFlatDimensionLT M (n + 1)

/-- **3.1, rings** The flat dimension, in `WithBot ℕ∞`, `⊥` exactly for the zero module. -/
noncomputable def flatDimension (M : ModuleCat.{v} A) : WithBot ℕ∞ :=
  sInf {d : WithBot ℕ∞ | ∀ i : ℕ, d < i → HasFlatDimensionLT M i}

theorem flatDimension_eq_bot_iff (M : ModuleCat.{v} A) : flatDimension M = ⊥ ↔ IsZero M :=
  sorry

/-- **3.1, rings** Flat dimension `≤ 0` is flatness. -/
theorem hasFlatDimensionLE_zero_iff (M : ModuleCat.{v} A) :
    HasFlatDimensionLE M 0 ↔ Module.BalancedFlat A M :=
  sorry

/-- **3.1, rings: the classical definition**: flat dimension `≤ n`; `Tor_i^A(-, M) = 0` for
`i > n`; `Tor_{n+1}^A(-, M) = 0`; the `n`-th syzygy of every, or of some, projective resolution
is flat. -/
theorem hasFlatDimensionLE_tfae (M : ModuleCat.{v} A) (n : ℕ) :
    List.TFAE
      [HasFlatDimensionLE M n,
        ∀ (N : ModuleCat.{v} Aᵐᵒᵖ) (i : ℕ), n < i →
          IsZero (((BalancedTor.{v} ℤ A i).obj N).obj M),
        ∀ N : ModuleCat.{v} Aᵐᵒᵖ, IsZero (((BalancedTor.{v} ℤ A (n + 1)).obj N).obj M),
        ∀ P : ProjectiveResolution M, Module.BalancedFlat A (P.complex.opcycles n),
        ∃ P : ProjectiveResolution M, Module.BalancedFlat A (P.complex.opcycles n)] :=
  sorry

theorem flatDimension_le_projectiveDimension (M : ModuleCat.{v} A) :
    flatDimension M ≤ projectiveDimension M :=
  sorry

/-- **3.1, rings: dimension shifting** along `0 → K → F → M → 0` with `F` flat. -/
theorem hasFlatDimensionLE_succ_iff {S : ShortComplex (ModuleCat.{v} A)} (hS : S.ShortExact)
    [Module.BalancedFlat A S.X₂] (n : ℕ) :
    HasFlatDimensionLE S.X₃ (n + 1) ↔ HasFlatDimensionLE S.X₁ n :=
  sorry

/-- **3.1, rings: character modules** The flat dimension of `M` is the injective dimension of its
character module ([Lam-LMR, (5.57)]): the case `R = ℤ`, `E = ℚ ⧸ ℤ` of the categorical
duality. -/
theorem flatDimension_eq_injectiveDimension_characterModule (M : ModuleCat.{v} A) :
    flatDimension M = injectiveDimension (ModuleCat.of Aᵐᵒᵖ (CharacterModule M)) :=
  sorry

/-- **3.1, rings** Ring flat dimension is flat dimension over `SingleObj A` (0.2). -/
theorem hasFlatDimensionLT_iff_singleObj {A : Type u} [Ring A] (M : ModuleCat.{u} A) (n : ℕ) :
    HasFlatDimensionLT M n ↔
      LeftModCat.HasFlatDimensionLT ((moduleCatEquivLeftModCat.{u} A).functor.obj M) n :=
  sorry

end RingFlatDimension

/-! ### 3.2 Global dimension of an abelian category -/

section GlobalDimension

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]

/-- **3.2** The global dimension of an abelian category: the supremum of the projective dimensions
of its objects ([Mitchell, §9, p. 42]). Tau Ceti's ring `TauCeti.globalDimension` is the case
`ModuleCat A`, and becomes this special case. -/
noncomputable def Abelian.globalDimension : WithBot ℕ∞ :=
  ⨆ X : 𝒜, projectiveDimension X

variable {𝒜} in
theorem Abelian.projectiveDimension_le_globalDimension (X : 𝒜) :
    projectiveDimension X ≤ Abelian.globalDimension 𝒜 :=
  le_iSup (fun X : 𝒜 ↦ projectiveDimension X) X

theorem Abelian.globalDimension_le_iff (n : ℕ) :
    Abelian.globalDimension 𝒜 ≤ n ↔ ∀ X : 𝒜, HasProjectiveDimensionLE X n := by
  simp [Abelian.globalDimension, projectiveDimension_le_iff]

theorem Abelian.globalDimension_eq_bot_iff :
    Abelian.globalDimension 𝒜 = ⊥ ↔ ∀ X : 𝒜, IsZero X := by
  simp [Abelian.globalDimension, projectiveDimension_eq_bot_iff]

/-- **3.2** The global dimension is also the supremum of the injective dimensions: both say that
`Ext^i` vanishes for `i` above the bound. -/
theorem Abelian.globalDimension_eq_iSup_injectiveDimension :
    Abelian.globalDimension 𝒜 = ⨆ X : 𝒜, injectiveDimension X :=
  sorry

/-- **3.2** `gldim 𝒜ᵒᵖ = gldim 𝒜` ([Mitchell, §9, p. 42]). -/
theorem Abelian.globalDimension_opposite :
    Abelian.globalDimension 𝒜ᵒᵖ = Abelian.globalDimension 𝒜 :=
  sorry

/-- **3.2** Equivalent abelian categories have the same global dimension. -/
theorem Abelian.globalDimension_eq_of_equivalence {ℬ : Type*} [Category ℬ] [Abelian ℬ]
    (e : 𝒜 ≌ ℬ) : Abelian.globalDimension 𝒜 = Abelian.globalDimension ℬ :=
  sorry

/-- **3.2, rings**: Tau Ceti's `TauCeti.globalDimension A` is the global dimension of
`ModuleCat A`. After the refactor of main this is the definition. -/
theorem globalDimension_eq_abelianGlobalDimension (A : Type u) [Ring A] :
    TauCeti.globalDimension.{v} A = Abelian.globalDimension (ModuleCat.{v} A) := by
  rw [TauCeti.globalDimension_def]; rfl

end GlobalDimension

section ModCatGlobalDimension

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- **3.2, Auslander's lemma for `Mod C`**: the global dimension of the right modules is at most
`n` exactly when every cyclic module `Hom(-, X) ⧸ I` has projective dimension at most `n`
([Au, Thm. 1, p. 68] for rings). Route: an injective dimension bound (3.2) checked by the Baer
criterion of 2.2 on a cosyzygy. Main's `TauCeti.globalDimension_le_tfae` follows. -/
theorem ModCat.globalDimension_le_iff_cyclic [EssentiallySmall.{v} C] (n : ℕ) :
    Abelian.globalDimension (ModCat.{v} C) ≤ n ↔
      ∀ (X : C) (I : Subobject ((ModCat.yoneda C).obj X)),
        HasProjectiveDimensionLE (cokernel I.arrow) n :=
  sorry

/-- **3.2, Auslander's lemma for left modules**, with the cyclic modules `Hom(X, -) ⧸ I`. -/
theorem LeftModCat.globalDimension_le_iff_cyclic [EssentiallySmall.{v} C] (n : ℕ) :
    Abelian.globalDimension (LeftModCat.{v} C) ≤ n ↔
      ∀ (X : C) (I : Subobject ((LeftModCat.coyoneda C).obj (op X))),
        HasProjectiveDimensionLE (cokernel I.arrow) n :=
  sorry

/-- **3.2, sides**: the left global dimension of `C` is the right global dimension of `Cᵒᵖ`,
through the equivalence of 0.5. -/
theorem LeftModCat.globalDimension_eq_globalDimension_modCat_op :
    Abelian.globalDimension (LeftModCat.{w} C) = Abelian.globalDimension (ModCat.{w} Cᵒᵖ) :=
  sorry

/-- **3.2, universe independence**: both global dimensions are computed by the cyclic modules
of a small model, as Tau Ceti's `TauCeti.globalDimension_eq_globalDimension`. -/
theorem ModCat.globalDimension_eq_globalDimension [EssentiallySmall.{w} C]
    [EssentiallySmall.{t} C] :
    Abelian.globalDimension (ModCat.{w} C) = Abelian.globalDimension (ModCat.{t} C) :=
  sorry

/-- **3.2, rings**: the left global dimension of `A` is that of the left modules over
`SingleObj A` (0.2). -/
theorem globalDimension_eq_globalDimension_singleObj (A : Type u) [Ring A] :
    TauCeti.globalDimension.{u} A = Abelian.globalDimension (LeftModCat.{u} (SingleObj A)) :=
  sorry

end ModCatGlobalDimension

/-! ### 3.3 Weak global dimension -/

section WeakGlobalDimension

open ModCat

variable (C : Type u) [Category.{v} C] [Preadditive C] [EssentiallySmall.{v} C]

/-- **3.3** The weak global dimension of `C`: the supremum of the flat dimensions of the left
modules. It is left-right symmetric (`LeftModCat.weakGlobalDimension_op`). -/
noncomputable def LeftModCat.weakGlobalDimension : WithBot ℕ∞ :=
  ⨆ G : LeftModCat.{v} C, G.flatDimension

theorem LeftModCat.weakGlobalDimension_le_iff (n : ℕ) :
    LeftModCat.weakGlobalDimension C ≤ n ↔
      ∀ (F : ModCat.{v} C) (G : LeftModCat.{v} C), IsZero (((tor ℤ (n + 1)).obj F).obj G) :=
  sorry

/-- **3.3, symmetry** ([Au, p. 70]; [Lam-LMR, (5.63)] for rings): from the balance (1.3). -/
theorem LeftModCat.weakGlobalDimension_op :
    LeftModCat.weakGlobalDimension Cᵒᵖ = LeftModCat.weakGlobalDimension C :=
  sorry

/-- **3.3** The weak global dimension is also the supremum over the right modules (by the
definition over `Cᵒᵖ` and symmetry). -/
theorem LeftModCat.weakGlobalDimension_eq_iSup_modCat :
    LeftModCat.weakGlobalDimension C = ⨆ F : ModCat.{v} C, ModCat.flatDimension F :=
  sorry

/-- **3.3, universe-free tests**: `wgldim C ≤ n`; every cyclic right module `Hom(-, X) ⧸ I` with
`I` finitely generated has flat dimension `≤ n`; every finitely presented right module has flat
dimension `≤ n` ([Lam-LMR, (5.69)] for rings). By the definition of flat dimension, the second
item tests only `Tor` between finitely presented cyclic modules on both sides. -/
theorem LeftModCat.weakGlobalDimension_le_tfae (n : ℕ) :
    List.TFAE
      [LeftModCat.weakGlobalDimension C ≤ n,
        ∀ ⦃X : C⦄ ⦃m : ℕ⦄ ⦃Y : Fin m → C⦄ (β : ∀ j, Y j ⟶ X),
          ModCat.HasFlatDimensionLE (cokernel (ModCat.yonedaSpan β).arrow) n,
        ∀ F : ModCat.{v} C, IsFinitelyPresentable.{v} F → ModCat.HasFlatDimensionLE F n] :=
  sorry

/-- **3.3, bounds** by the left global dimension ([Lam-LMR, (5.58)] for rings). -/
theorem LeftModCat.weakGlobalDimension_le_globalDimension :
    LeftModCat.weakGlobalDimension C ≤ Abelian.globalDimension (LeftModCat.{v} C) :=
  sorry

/-- **3.3, bounds** by the right global dimension. -/
theorem LeftModCat.weakGlobalDimension_le_globalDimension_modCat :
    LeftModCat.weakGlobalDimension C ≤ Abelian.globalDimension (ModCat.{v} C) :=
  sorry

/-- **3.3, from projective dimension**: if every finitely presented right module has projective
dimension `≤ n`, then `wgldim C ≤ n`. Consumer: ArtinAlgebras §7.5. -/
theorem LeftModCat.weakGlobalDimension_le_of_forall_isFinitelyPresentable (n : ℕ)
    (h : ∀ F : ModCat.{v} C, IsFinitelyPresentable.{v} F → HasProjectiveDimensionLE F n) :
    LeftModCat.weakGlobalDimension C ≤ n :=
  sorry

theorem LeftModCat.weakGlobalDimension_eq_bot_iff :
    LeftModCat.weakGlobalDimension C = ⊥ ↔ ∀ X : C, IsZero X :=
  sorry

theorem LeftModCat.weakGlobalDimension_le_zero_iff :
    LeftModCat.weakGlobalDimension C ≤ 0 ↔ ∀ G : LeftModCat.{v} C, G.Flat :=
  sorry

end WeakGlobalDimension

section RingWeakGlobalDimension

variable {A : Type u} [Ring A] [Small.{v} A]

variable (A) in
/-- **3.3, rings** The weak global dimension, native. -/
noncomputable def weakGlobalDimension : WithBot ℕ∞ :=
  ⨆ M : ModuleCat.{v} A, flatDimension M

theorem weakGlobalDimension_le_iff (n : ℕ) :
    weakGlobalDimension.{v} A ≤ n ↔
      ∀ (N : ModuleCat.{v} Aᵐᵒᵖ) (M : ModuleCat.{v} A),
        IsZero (((BalancedTor.{v} ℤ A (n + 1)).obj N).obj M) :=
  sorry

variable (A) in
/-- **3.3, rings: symmetry** ([Au, p. 70]; [Lam-LMR, (5.63)]). -/
theorem weakGlobalDimension_mulOpposite :
    weakGlobalDimension.{v} Aᵐᵒᵖ = weakGlobalDimension.{v} A :=
  sorry

variable (A) in
/-- **3.3, rings: bounds** by the left global dimension ([Lam-LMR, (5.58)]). -/
theorem weakGlobalDimension_le_globalDimension :
    weakGlobalDimension.{v} A ≤ TauCeti.globalDimension.{v} A :=
  sorry

variable (A) in
/-- **3.3, rings: bounds** by the right global dimension. -/
theorem weakGlobalDimension_le_globalDimension_mulOpposite :
    weakGlobalDimension.{v} A ≤ TauCeti.globalDimension.{v} Aᵐᵒᵖ :=
  sorry

/-- **3.3, rings: tests**: finitely presented right modules, and cyclic right modules with
finitely generated relations ([Lam-LMR, (5.69)]). -/
theorem weakGlobalDimension_le_tfae (n : ℕ) :
    List.TFAE
      [weakGlobalDimension.{v} A ≤ n,
        ∀ N : ModuleCat.{v} Aᵐᵒᵖ, Module.FinitePresentation Aᵐᵒᵖ N → flatDimension N ≤ n,
        ∀ I : Submodule Aᵐᵒᵖ A, I.FG →
          flatDimension (ModuleCat.of Aᵐᵒᵖ (Shrink.{v} (A ⧸ I))) ≤ n] :=
  sorry

/-- **3.3, rings: from projective dimension**. -/
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

/-- **3.3, rings**: the ring weak global dimension is that of `SingleObj A`. -/
theorem weakGlobalDimension_eq_weakGlobalDimension_singleObj (A : Type u) [Ring A] :
    weakGlobalDimension.{u} A = LeftModCat.weakGlobalDimension (SingleObj A) :=
  sorry

end RingWeakGlobalDimension

/-! ### 3.4 Auslander's theorem -/

section Auslander

variable {C : Type u} [Category.{v} C] [Preadditive C] [EssentiallySmall.{v} C]

/-- **3.4, the `FP_∞` lemma**: a module with a projective resolution by finitely presented
projectives has equal flat and projective dimension. No Noetherian hypothesis. Route: if the flat
dimension is `n`, the `n`-th syzygy `coker (P_{n+1} → P_n)` is finitely presented and flat (3.1),
hence projective (2.3). -/
theorem LeftModCat.flatDimension_eq_projectiveDimension_of_projectiveResolution
    (G : LeftModCat.{v} C) (P : ProjectiveResolution G)
    (hP : ∀ i, IsFinitelyPresentable.{v} (P.complex.X i)) :
    G.flatDimension = projectiveDimension G :=
  sorry

variable (C)

/-- **3.4, Auslander's theorem** ([Au, Thm. 4, p. 70]; [Lam-LMR, (5.59)] for rings): if every
representable `Hom(X, -)` is a Noetherian object (`C` is left Noetherian), the global dimension of
the left modules equals the weak global dimension. Route: the cyclic modules of 3.2 have
resolutions by finitely presented projectives, then the `FP_∞` lemma. An adaptation of the ring
theorem. -/
theorem LeftModCat.globalDimension_eq_weakGlobalDimension
    [∀ X : C, IsNoetherianObject ((LeftModCat.coyoneda C).obj (op X))] :
    Abelian.globalDimension (LeftModCat.{v} C) = LeftModCat.weakGlobalDimension C :=
  sorry

/-- **3.4** The right-module form: if every `Hom(-, X)` is a Noetherian object, the global
dimension of `Mod C` equals the weak global dimension (over `Cᵒᵖ` and 3.3's symmetry). -/
theorem ModCat.globalDimension_eq_weakGlobalDimension
    [∀ X : C, IsNoetherianObject ((ModCat.yoneda C).obj X)] :
    Abelian.globalDimension (ModCat.{v} C) = LeftModCat.weakGlobalDimension C :=
  sorry

/-- **3.4, left bound**: for a left Noetherian `C`, a bound on the projective dimension of the
finitely presented right modules bounds the left global dimension (3.3 and the theorem). No
right Noetherian hypothesis. -/
theorem LeftModCat.globalDimension_le_of_forall_isFinitelyPresentable
    [∀ X : C, IsNoetherianObject ((LeftModCat.coyoneda C).obj (op X))] (n : ℕ)
    (h : ∀ F : ModCat.{v} C, IsFinitelyPresentable.{v} F → HasProjectiveDimensionLE F n) :
    Abelian.globalDimension (LeftModCat.{v} C) ≤ n :=
  sorry

/-- **3.4, symmetry**: for a left and right Noetherian `C`, the left and right global dimensions
agree ([Au, Cor. 5, p. 70] for rings). -/
theorem ModCat.globalDimension_eq_globalDimension_leftModCat
    [∀ X : C, IsNoetherianObject ((LeftModCat.coyoneda C).obj (op X))]
    [∀ X : C, IsNoetherianObject ((ModCat.yoneda C).obj X)] :
    Abelian.globalDimension (ModCat.{v} C) = Abelian.globalDimension (LeftModCat.{v} C) :=
  sorry

end Auslander

section RingAuslander

variable {A : Type u} [Ring A] [Small.{v} A]

/-- **3.4, rings: the `FP_∞` lemma** for a projective resolution by finite projectives. -/
theorem flatDimension_eq_projectiveDimension_of_projectiveResolution (M : ModuleCat.{v} A)
    (P : ProjectiveResolution M) (hP : ∀ i, Module.Finite A (P.complex.X i)) :
    flatDimension M = projectiveDimension M :=
  sorry

/-- **3.4, rings** Over a left Noetherian ring, a finite module has equal flat and projective
dimension. -/
theorem flatDimension_eq_projectiveDimension_of_finite [IsNoetherianRing A] (M : ModuleCat.{v} A)
    [Module.Finite A M] : flatDimension M = projectiveDimension M :=
  sorry

variable (A) in
/-- **3.4, rings: Auslander's theorem**: a left Noetherian ring has equal left global and weak
global dimension. -/
theorem globalDimension_eq_weakGlobalDimension [IsNoetherianRing A] :
    TauCeti.globalDimension.{v} A = weakGlobalDimension.{v} A :=
  sorry

/-- **3.4, rings: left bound**: over a left Noetherian ring, a bound on the projective dimension
of the finitely presented right modules bounds the left global dimension. Consumer:
ArtinAlgebras §7.5. -/
theorem globalDimension_le_of_forall_finitePresentation_mulOpposite [IsNoetherianRing A] (n : ℕ)
    (h : ∀ N : ModuleCat.{v} Aᵐᵒᵖ, Module.FinitePresentation Aᵐᵒᵖ N →
      HasProjectiveDimensionLE N n) :
    TauCeti.globalDimension.{v} A ≤ n :=
  sorry

end RingAuslander

/-! ### 3.5 Kernels of flat modules and countably presented flat modules -/

section Extras

variable {C : Type u} [Category.{v} C] [Preadditive C] [EssentiallySmall.{v} C]

variable (C) in
/-- **3.5** The flat right modules are closed under kernels exactly when the weak global dimension
is at most two ([CB, Thm. 2.3, p. 1651]). Route: dimension shifting along
`0 → ker f → F → F' → coker f → 0`. -/
theorem ModCat.forall_flat_kernel_iff :
    (∀ ⦃F F' : ModCat.{v} C⦄ (f : F ⟶ F'), ModCat.Flat F → ModCat.Flat F' →
      ModCat.Flat (kernel f)) ↔ LeftModCat.weakGlobalDimension C ≤ 2 :=
  sorry

/-- **3.5** The colimit of a sequence of projective modules has projective dimension at most one:
the telescope `0 → ⊕ D_i → ⊕ D_i → colim D → 0`, as for Bass's module (2.5). -/
theorem LeftModCat.hasProjectiveDimensionLE_one_colimit (D : ℕ ⥤ LeftModCat.{v} C)
    [∀ i, Projective (D.obj i)] : HasProjectiveDimensionLE (colimit D) 1 :=
  sorry

/-- **3.5, Jensen**: a countably presented (`ℵ₁`-presentable) flat module has projective dimension
at most one. Route: Lazard (2.3) writes it as the colimit of a sequence of finite sums of
representables; then the telescope. -/
theorem LeftModCat.Flat.hasProjectiveDimensionLE_one (G : LeftModCat.{v} C) [G.Flat]
    [Fact (Cardinal.aleph.{v} 1).IsRegular] [IsCardinalPresentable G (Cardinal.aleph.{v} 1)] :
    HasProjectiveDimensionLE G 1 :=
  sorry

end Extras

/-! ## Layer 4: semiperfect and perfect categories, and Bass's Theorem P

Category-primary. `J(C)` is Tau Ceti's radical `TauCeti.jacobsonRadicalIdeal C`, and `C ⧸ J(C)` is
the quotient category `(TauCeti.jacobsonRadicalIdeal C).Quotient`. Modules are left modules
(covariant functors), as in [Simson] and [Harada]. A projective cover is an essential epimorphism
(`TauCeti.IsEssentialEpi`) from a projective object. The statements are in the universe `v` of the
morphisms, where the representables and Bass's modules (2.5) live; the README states them for
`EssentiallySmall.{w} C`. Rings keep native classes with `SingleObj` bridges, and the ring theorems
are derived from the categorical ones. -/

/-! ### 4.1 T-nilpotence and Nakayama's lemma for all modules -/

section TNilpotentCategory

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- **4.1** An ideal `I` of `C` is **left T-nilpotent** if for every chain `c₀ ← c₁ ← ⋯` with every
`f i ∈ I` some composite `p_n = f (n - 1) ≫ ⋯ ≫ f 0 : c n ⟶ c 0` vanishes ([Simson, p. 108]). For
`C = SingleObj A`, `p_n = a₀ a₁ ⋯ aₙ₋₁` (Mathlib's `f ≫ g = g * f`): Bass's left T-nilpotence. -/
def MorphismIdeal.IsLeftTNilpotent (I : TauCeti.MorphismIdeal C) : Prop :=
  ∀ (c : ℕ → C) (f : ∀ i, c (i + 1) ⟶ c i), (∀ i, f i ∈ I.hom (c (i + 1)) (c i)) →
    ∃ n : ℕ, (Functor.ofOpSequence f).map (homOfLE (Nat.zero_le n)).op = 0

/-- **4.1** Right T-nilpotence: left T-nilpotence of the opposite ideal on `Cᵒᵖ`, that is, of the
chains `c₀ → c₁ → ⋯`. -/
def MorphismIdeal.IsRightTNilpotent (I : TauCeti.MorphismIdeal C) : Prop :=
  MorphismIdeal.IsLeftTNilpotent I.op

theorem MorphismIdeal.IsLeftTNilpotent.mono {I I' : TauCeti.MorphismIdeal C}
    (h : MorphismIdeal.IsLeftTNilpotent I') (hI : I ≤ I') : MorphismIdeal.IsLeftTNilpotent I :=
  fun c f hf ↦ h c f fun i ↦ TauCeti.MorphismIdeal.le_def.mp hI _ (hf i)

/-- **4.1** A nilpotent ideal is left T-nilpotent. -/
theorem MorphismIdeal.isLeftTNilpotent_of_pow_eq_bot {I : TauCeti.MorphismIdeal C} {n : ℕ}
    (h : I ^ n = ⊥) : MorphismIdeal.IsLeftTNilpotent I :=
  sorry

/-- **4.1** A nilpotent ideal is right T-nilpotent. -/
theorem MorphismIdeal.isRightTNilpotent_of_pow_eq_bot {I : TauCeti.MorphismIdeal C} {n : ℕ}
    (h : I ^ n = ⊥) : MorphismIdeal.IsRightTNilpotent I :=
  sorry

/-- **4.1** `I · M` is **superfluous** in `M`: a map `g : N ⟶ M` whose image generates `M` together
with `I · M` is an epimorphism. -/
def MorphismIdeal.IsSuperfluousSmul (I : TauCeti.MorphismIdeal C) (M : LeftModCat.{w} C) : Prop :=
  ∀ ⦃N : LeftModCat.{w} C⦄ (g : N ⟶ M),
    (∀ c, MorphismIdeal.smul I M c ⊔ (g.hom.app c).hom.range = ⊤) → Epi g

/-- **4.1, Bass's Nakayama lemma** in every universe ([Simson, Lemma 5.3, p. 108]): for a left
T-nilpotent `I`, `I · M = M` implies `M = 0`. Route: keep `M(p_n)(x_n) ≠ 0` by dependent choice;
[Bass, pp. 473–474] uses König's graph theorem instead. -/
theorem MorphismIdeal.IsLeftTNilpotent.isZero_of_smul_eq_top {I : TauCeti.MorphismIdeal C}
    (hI : MorphismIdeal.IsLeftTNilpotent I) (M : LeftModCat.{w} C)
    (h : ∀ c, MorphismIdeal.smul I M c = ⊤) : IsZero M :=
  sorry

/-- **4.1** For a left T-nilpotent `I`, `I · M` is superfluous in every module, in every
universe. -/
theorem MorphismIdeal.IsLeftTNilpotent.isSuperfluousSmul {I : TauCeti.MorphismIdeal C}
    (hI : MorphismIdeal.IsLeftTNilpotent I) (M : LeftModCat.{w} C) :
    MorphismIdeal.IsSuperfluousSmul I M :=
  sorry

/-- **4.1, Nakayama's lemma for all modules**: (1) `I` is left T-nilpotent; (2) `I · M = M`
implies `M = 0`; (3) `I · M` is superfluous in every `M`. (1) ⇒ (2) by dependent choice, (2) ⇔ (3)
as usual, (2) ⇒ (1) through Bass's module `B` of an `I`-chain (2.5): `[𝟙 c₀] ≠ 0` while no `p_n`
vanishes, and `B = I · B`, since the class of `g : c i ⟶ d` is that of `f i ≫ g`, the image of
`[𝟙 (c (i + 1))]` under `B(f i ≫ g)` with `f i ≫ g ∈ I`. Stated in the universe `v`, where Bass's
module lives; (1) ⇒ (2), (3) hold in every universe. -/
theorem MorphismIdeal.isLeftTNilpotent_tfae (I : TauCeti.MorphismIdeal C) :
    List.TFAE
      [MorphismIdeal.IsLeftTNilpotent I,
        ∀ M : LeftModCat.{v} C, (∀ c, MorphismIdeal.smul I M c = ⊤) → IsZero M,
        ∀ M : LeftModCat.{v} C, MorphismIdeal.IsSuperfluousSmul I M] :=
  sorry

/-- **4.1** Left T-nilpotence through Bass's modules (2.5): `I` is left T-nilpotent exactly when
the Bass module of every chain in `I` is zero (tails of `I`-chains are `I`-chains). -/
theorem MorphismIdeal.isLeftTNilpotent_iff_forall_isZero_bassModule
    (I : TauCeti.MorphismIdeal C) :
    MorphismIdeal.IsLeftTNilpotent I ↔
      ∀ (c : ℕ → C) (f : ∀ i, c (i + 1) ⟶ c i), (∀ i, f i ∈ I.hom (c (i + 1)) (c i)) →
        IsZero (LeftModCat.bassModule c f) :=
  sorry

end TNilpotentCategory

section TNilpotent

variable {A : Type u} [Ring A]

/-- **4.1, rings** A subset `S` is **left T-nilpotent** if for every sequence `a₀, a₁, …` in `S`
some product `a₀ a₁ ⋯ aₙ₋₁` vanishes. -/
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

variable (A) in
/-- **4.1, rings** The ring notion is the categorical one at `SingleObj A`, for the Jacobson
radical: `p_n = a₀ ⋯ aₙ₋₁`. -/
theorem isLeftTNilpotent_jacobson_iff_singleObj :
    IsLeftTNilpotent (Ring.jacobson A : Set A) ↔
      MorphismIdeal.IsLeftTNilpotent (TauCeti.jacobsonRadicalIdeal (SingleObj A)) :=
  sorry

/-- **4.1, rings: Nakayama's lemma for all modules**, a corollary of the categorical form through
`SingleObj A` (0.2), where `I · M` is `J • ⊤`. -/
theorem isLeftTNilpotent_tfae (J : Ideal A) :
    List.TFAE
      [IsLeftTNilpotent (J : Set A),
        ∀ (M : Type u) [AddCommGroup M] [Module A M], J • (⊤ : Submodule A M) = ⊤ → Subsingleton M,
        ∀ (M : Type u) [AddCommGroup M] [Module A M],
          TauCeti.IsSuperfluous (J • (⊤ : Submodule A M)),
        TauCeti.IsSuperfluous (J • (⊤ : Submodule A (ℕ →₀ A)))] :=
  sorry

/-- **4.1, rings** For a left T-nilpotent left ideal, `J • M` is superfluous in every module, in
every universe. -/
theorem IsLeftTNilpotent.isSuperfluous_smul_top {J : Ideal A} (hJ : IsLeftTNilpotent (J : Set A))
    (M : Type w) [AddCommGroup M] [Module A M] : TauCeti.IsSuperfluous (J • (⊤ : Submodule A M)) :=
  sorry

end TNilpotent

/-! ### 4.2 Semilocal and semiperfect rings and categories -/

section Semilocal

/-- **4.2** A ring is **semilocal** if `R ⧸ J` is a semisimple ring. The ladder:
`IsSemiprimaryRing` ⇒ `IsLeftPerfectRing` ⇒ `TauCeti.IsSemiperfectRing` ⇒ `IsSemilocalRing`. -/
class IsSemilocalRing (R : Type u) [Ring R] : Prop where
  isSemisimpleRing : IsSemisimpleRing (R ⧸ Ring.jacobson R)

attribute [instance] IsSemilocalRing.isSemisimpleRing

variable {R : Type u} [Ring R]

/-- **4.2** Semilocality is left-right symmetric. -/
instance [IsSemilocalRing R] : IsSemilocalRing Rᵐᵒᵖ :=
  ⟨(TauCeti.Ring.isSemisimpleRing_quotient_jacobson_mulOpposite_iff R).mpr inferInstance⟩

/-- **4.2** A semiperfect ring is semilocal. After the refactor of Tau Ceti's
`TauCeti.IsSemiperfectRing` to `extends IsSemilocalRing`, this is the `extends` projection. -/
instance [TauCeti.IsSemiperfectRing R] : IsSemilocalRing R :=
  ⟨inferInstance⟩

/-- **4.2** Surjective images of semilocal rings are semilocal. -/
theorem IsSemilocalRing.of_surjective {S : Type*} [Ring S] [IsSemilocalRing R] (f : R →+* S)
    (hf : Function.Surjective f) : IsSemilocalRing S :=
  sorry

/-- **4.2** A commutative ring is semilocal exactly when it has finitely many maximal ideals. -/
theorem isSemilocalRing_iff_finite_isMaximal {R : Type u} [CommRing R] :
    IsSemilocalRing R ↔ {I : Ideal R | I.IsMaximal}.Finite :=
  sorry

/-- **4.2** Semiperfectness is left-right symmetric. -/
instance IsSemiperfectRing.mulOpposite [TauCeti.IsSemiperfectRing R] :
    TauCeti.IsSemiperfectRing Rᵐᵒᵖ :=
  sorry

/-- **4.2** A corner `eRe` of a semiperfect ring is semiperfect. -/
theorem IsSemiperfectRing.corner [TauCeti.IsSemiperfectRing R] {e : R} (he : IsIdempotentElem e) :
    TauCeti.IsSemiperfectRing he.Corner :=
  sorry

end Semilocal

section SemilocalCategory

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- **4.2** A preadditive category is **semilocal** if every endomorphism ring is semilocal. -/
class IsSemilocalCategory : Prop where
  isSemilocalRing_end (X : C) : IsSemilocalRing (End X)

attribute [instance] IsSemilocalCategory.isSemilocalRing_end

variable {C} in
/-- **4.2** A left module is **semisimple** if its subobjects are complemented. -/
abbrev LeftModCat.IsSemisimple (M : LeftModCat.{w} C) : Prop :=
  ComplementedLattice (Subobject M)

/-- **4.2** `C` is **semisimple** in Simson's sense ([Simson, p. 93]): every representable left
module `Hom(X, -)` is semisimple. -/
def IsSemisimpleCategory : Prop :=
  ∀ X : C, LeftModCat.IsSemisimple ((LeftModCat.coyoneda C).obj (op X))

/-- **4.2, regularity of `C ⧸ J(C)`** (agent-proved, not from a source). For `f : X ⟶ Y` in
`D = C ⧸ J(C)`, the left ideal `{g ∘ f}` of the semisimple ring `End X` is `End(X) e` with
`e = g₀ ∘ f` idempotent; `u = f ∘ (1 - e)` has `g ∘ u = 0` for every `g`, so it is radical, hence
zero in `D`; so `f = f ∘ g₀ ∘ f`. -/
theorem IsSemilocalCategory.exists_comp_comp_eq_self [IsSemilocalCategory C]
    {X Y : (TauCeti.jacobsonRadicalIdeal C).Quotient} (f : X ⟶ Y) : ∃ g : Y ⟶ X, f ≫ g ≫ f = f :=
  sorry

/-- **4.2** `C` is semilocal exactly when `C ⧸ J(C)` is semisimple in Simson's sense. Route:
[Simson, Prop. 1.2, p. 93] (semisimple ⇔ von Neumann regular with semisimple endomorphism rings),
`End_{C ⧸ J}(X) = End X ⧸ Ring.jacobson (End X)`, and the regularity above. -/
theorem isSemilocalCategory_iff_isSemisimpleCategory :
    IsSemilocalCategory C ↔ IsSemisimpleCategory (TauCeti.jacobsonRadicalIdeal C).Quotient :=
  sorry

/-- **4.2** `Cᵒᵖ` is semilocal with `C`: `End (op X) = (End X)ᵐᵒᵖ`. -/
instance [IsSemilocalCategory C] : IsSemilocalCategory Cᵒᵖ :=
  sorry

/-- **4.2** A preadditive category is **semiperfect** if every endomorphism ring is semiperfect. -/
class IsSemiperfectCategory : Prop extends IsSemilocalCategory C where
  isSemiperfectRing_end (X : C) : TauCeti.IsSemiperfectRing (End X)

attribute [instance] IsSemiperfectCategory.isSemiperfectRing_end

/-- **4.2** A Krull–Schmidt category is semiperfect (Tau Ceti's
`TauCeti.IsKrullSchmidt.isSemiperfectRing_end`). -/
instance IsKrullSchmidt.isSemiperfectCategory [HasFiniteBiproducts C] [TauCeti.IsKrullSchmidt C] :
    IsSemiperfectCategory C where
  isSemilocalRing_end _ := inferInstance
  isSemiperfectRing_end _ := inferInstance

/-- **4.2, Krause's criterion with the class**: a category with finite biproducts is Krull–Schmidt
exactly when idempotents split and it is semiperfect. Restates Tau Ceti's
`TauCeti.isKrullSchmidt_iff_isIdempotentComplete_and_isSemiperfectRing_end` (downstream refactor,
no alias). -/
theorem isKrullSchmidt_iff_isIdempotentComplete_and_isSemiperfectCategory [HasFiniteBiproducts C] :
    TauCeti.IsKrullSchmidt C ↔ IsIdempotentComplete C ∧ IsSemiperfectCategory C := by
  rw [TauCeti.isKrullSchmidt_iff_isIdempotentComplete_and_isSemiperfectRing_end]
  exact and_congr_right fun _ ↦
    ⟨fun h ↦ { isSemilocalRing_end := fun X ↦ have := h X; inferInstance
               isSemiperfectRing_end := h },
      fun h ↦ h.isSemiperfectRing_end⟩

/-- **4.2** Finite biproducts pass to `Cᵒᵖ` (finite coproducts of `C` are finite products of
`Cᵒᵖ`); not an instance in Mathlib. -/
instance [HasFiniteBiproducts C] : HasFiniteBiproducts Cᵒᵖ :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- **4.2** The opposite of a Krull–Schmidt category is Krull–Schmidt: Krause's criterion, with
`End (op X) = (End X)ᵐᵒᵖ` and `IsSemiperfectRing.mulOpposite`. -/
instance [HasFiniteBiproducts C] [TauCeti.IsKrullSchmidt C] : TauCeti.IsKrullSchmidt Cᵒᵖ :=
  sorry

end SemilocalCategory

/-- **4.2** `M` has a **projective cover**: an essential epimorphism (Tau Ceti's
`TauCeti.IsEssentialEpi`) from a projective object. Over `ModuleCat A` this is Tau Ceti's
`TauCeti.IsProjectiveCover` (`TauCeti.isProjectiveCover_iff_forall_surjective`). -/
def HasProjectiveCover {𝒜 : Type*} [Category 𝒜] (M : 𝒜) : Prop :=
  ∃ (P : 𝒜) (p : P ⟶ M), Projective P ∧ TauCeti.IsEssentialEpi p

section SemiperfectCategory

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- **4.2, semiperfect categories by projective covers** ([Simson, Thm. 5.6, p. 110];
[Krause, Prop. 4.1]): (1) `C` is semiperfect; (2) every `Hom(X, -)` is a finite sum of projective
modules with local endomorphism rings; (3) every finitely generated left module has a projective
cover; (4) every simple left module has one; (5) `proj C` is Krull–Schmidt. For (5): `proj C` has
finite biproducts and split idempotents (0.8), so Krause's criterion applies, with
`End Hom(-, X) = End X`, finite sums and corners. -/
theorem isSemiperfectCategory_tfae :
    List.TFAE
      [IsSemiperfectCategory C,
        ∀ X : C, ∃ (n : ℕ) (P : Fin n → LeftModCat.{v} C), (∀ i, Projective (P i)) ∧
          (∀ i, IsLocalRing (End (P i))) ∧ Nonempty ((LeftModCat.coyoneda C).obj (op X) ≅ ∐ P),
        ∀ M : LeftModCat.{v} C, M.IsFinitelyGenerated → HasProjectiveCover M,
        ∀ S : LeftModCat.{v} C, Simple S → HasProjectiveCover S,
        TauCeti.IsKrullSchmidt (ModCat.proj C).FullSubcategory] :=
  sorry

variable {C}

/-- **4.2** Over a semiperfect `C` a simple left module `S` has a projective cover, by a summand
`Hom(X, -) e`: `S(X) ≠ 0` for some `X`; `1 = e₁ + ⋯ + eₙ` in `End X` with local corners; some
`eᵢ` does not kill a nonzero `x ∈ S(X)`, and `Hom(X, -) eᵢ`, projective with local endomorphism
ring, maps onto `S`. Theorem P uses only this and (1) of the TFAE. -/
theorem LeftModCat.hasProjectiveCover_of_simple [IsSemiperfectCategory C] (S : LeftModCat.{v} C)
    [Simple S] : HasProjectiveCover S :=
  sorry

end SemiperfectCategory

section Semiperfect

/-! #### 4.2, rings (TauCetiProject/TauCeti#38013, Part 3) -/

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
/-- **4.2, semiperfect rings by projective covers** (Sandomierski; Krause, Proposition 4.1), with
the item "finitely generated projective modules form a Krull–Schmidt category" (Krause's criterion,
as in the categorical form). -/
theorem isSemiperfectRing_tfae :
    List.TFAE
      [TauCeti.IsSemiperfectRing R,
        ∃ (n : ℕ) (P : Fin n → Type u) (_ : ∀ i, AddCommGroup (P i)) (_ : ∀ i, Module R (P i)),
          (∀ i, Module.Projective R (P i)) ∧ (∀ i, IsLocalRing (Module.End R (P i))) ∧
            Nonempty (R ≃ₗ[R] ∀ i, P i),
        ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M], ∃ (P : Type u)
          (_ : AddCommGroup P) (_ : Module R P) (p : P →ₗ[R] M), TauCeti.IsProjectiveCover p,
        ∀ (S : Type u) [AddCommGroup S] [Module R S] [IsSimpleModule R S], ∃ (P : Type u)
          (_ : AddCommGroup P) (_ : Module R P) (p : P →ₗ[R] S), TauCeti.IsProjectiveCover p,
        TauCeti.IsKrullSchmidt (TauCeti.finiteProjectiveModules R).FullSubcategory] :=
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

/-! ### 4.3 Left perfect rings and categories -/

section PerfectCategory

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- **4.3** A preadditive category is **left perfect** if it is semilocal and `J(C)` is left
T-nilpotent; by 4.2 this is Simson's condition: `J(C)` left T-nilpotent and `C ⧸ J(C)` semisimple.
Right perfect is `IsLeftPerfectCategory Cᵒᵖ`. -/
class IsLeftPerfectCategory : Prop extends IsSemilocalCategory C where
  isLeftTNilpotent : MorphismIdeal.IsLeftTNilpotent (TauCeti.jacobsonRadicalIdeal C)

variable {C}

/-- **4.3** A left perfect category is semiperfect: `J(End X)` is left T-nilpotent, hence nil, so
idempotents lift. -/
instance [IsLeftPerfectCategory C] : IsSemiperfectCategory C :=
  sorry

/-- **4.3** A semilocal category with nilpotent radical is left perfect (4.1). -/
theorem IsLeftPerfectCategory.of_pow_eq_bot [IsSemilocalCategory C] {n : ℕ}
    (h : TauCeti.jacobsonRadicalIdeal C ^ n = ⊥) : IsLeftPerfectCategory C :=
  sorry

/-- **4.3** A semilocal category with nilpotent radical is right perfect (4.1). -/
theorem IsLeftPerfectCategory.op_of_pow_eq_bot [IsSemilocalCategory C] {n : ℕ}
    (h : TauCeti.jacobsonRadicalIdeal C ^ n = ⊥) : IsLeftPerfectCategory Cᵒᵖ :=
  sorry

end PerfectCategory

section Perfect

/-- **4.3** A ring is **left perfect** if it is semilocal and `J` is left T-nilpotent. Right
perfect is `IsLeftPerfectRing Aᵐᵒᵖ`. -/
class IsLeftPerfectRing (A : Type u) [Ring A] : Prop extends IsSemilocalRing A where
  isLeftTNilpotent : IsLeftTNilpotent (Ring.jacobson A : Set A)

variable {A : Type u} [Ring A]

/-- **4.3** A semiprimary ring is left perfect (an instance in Tau Ceti); with
`TauCeti.IsSemiprimaryRing.mulOpposite` also right perfect. -/
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

variable (A) in
/-- **4.3, bridge**: `p_n = a₀ ⋯ aₙ₋₁` at `SingleObj A`. -/
theorem isLeftPerfectRing_iff_singleObj :
    IsLeftPerfectRing A ↔ IsLeftPerfectCategory (SingleObj A) :=
  sorry

end Perfect

/-! ### 4.4 Projective covers over left perfect categories -/

/-- **4.4** Over a left perfect `C` every left module has a projective cover ([Simson, Thm. 5.4,
(7) ⇒ (8), p. 109]; [Bass, Lemma 2.6, p. 473]). Route: `M ⧸ J · M` is a semisimple module over
`C ⧸ J(C)` (4.2); its simple summands have covers `Hom(X, -) e` (4.2); the sum of these lifts to
`M`, onto because `J · M` is superfluous (4.1), with kernel in the superfluous `J · P`. -/
theorem IsLeftPerfectCategory.hasProjectiveCover {C : Type u} [Category.{v} C] [Preadditive C]
    [EssentiallySmall.{v} C] [IsLeftPerfectCategory C] (M : LeftModCat.{v} C) :
    HasProjectiveCover M :=
  sorry

/-- **4.4, rings** Over a left perfect ring every module, in every universe, has a projective
cover, in the form of Tau Ceti's `TauCeti.exists_isProjectiveCover`, which it generalizes from
semiprimary rings. -/
theorem IsLeftPerfectRing.exists_isProjectiveCover {A : Type u} [Ring A] [IsLeftPerfectRing A]
    (M : Type v) [AddCommGroup M] [Module A M] :
    ∃ P : Submodule A (M →₀ A),
      TauCeti.IsProjectiveCover (Finsupp.linearCombination A id ∘ₗ P.subtype) :=
  sorry

/-! ### 4.5 Bass's Theorem P -/

section TheoremP

variable {C : Type u} [Category.{v} C] [Preadditive C] [EssentiallySmall.{v} C]

/-- **4.5, Villamayor step** ([Lam-LMR, (4.23), p. 129] for rings): in a short exact sequence
`0 → K → P → M → 0` with `P` projective and `M` flat, every element `x ∈ K(c)` is fixed by some
`θ : P ⟶ K`. Route: `P` is a summand of a free `F`; `x` lies in a finite subsum `L`; the 2.3
factorization of `L ⧸ (x) → M` through a finitely generated free `G` gives `θ = (ι - βα) ∘ π_L`. -/
theorem LeftModCat.exists_hom_app_apply_eq_of_flat {S : ShortComplex (LeftModCat.{v} C)}
    (hS : S.ShortExact) [Projective S.X₂] [LeftModCat.Flat S.X₃] (c : C) (x : S.X₁.obj.obj c) :
    ∃ θ : S.X₂ ⟶ S.X₁, (θ.hom.app c).hom ((S.f.hom.app c).hom x) = x :=
  sorry

/-- **4.5, the Mares–Simson lemma** ([Simson, Thm. 5.4, (9′) ⇒ (1′), pp. 109–110], with the
argument of [Mares, Thm. 2.4, proof part (i), p. 349]): a flat module with a projective cover is
projective. Any `C`, no radical hypothesis. Route: for the cover `0 → K → P → M → 0` and `x ∈ K`,
take `θ` from the Villamayor step; `s = i ∘ θ` has image in the superfluous `K`, so `1 - s` is onto,
splits, and its kernel is a summand inside `K`, hence zero; but `(1 - s) x = 0`. Agent assembly of
Mares, Simson and Villamayor. -/
theorem LeftModCat.Flat.projective_of_isEssentialEpi {P M : LeftModCat.{v} C} [Projective P]
    [LeftModCat.Flat M] (p : P ⟶ M) (hp : TauCeti.IsEssentialEpi p) : Projective M :=
  sorry

variable (C) in
/-- **4.5, Bass's Theorem P for categories** ([Simson, Thm. 5.4, p. 108]; [Harada, Thm. 5,
p. 339]): (1) `C` is left perfect; (2) every left module has a projective cover; (2′) every
semisimple left module has one ([Sandomierski, Thm. 5, p. 206], rings); (3) every flat left module
is projective; (3′) every countably presented flat left module is projective; (4) for every `c`, the
principal right ideals `g C` into `c`, the images of `Hom(-, d) → Hom(-, c)`, satisfy the descending
chain condition; (4′) in every chain `c₀ ← c₁ ← ⋯` some `p_n` factors through every later `p_m`;
(5) flat and projective dimension agree; (6) filtered colimits of projective left modules are
projective. Route: 1 ⇒ 2 (4.4) ⇒ 3 (Mares–Simson) ⇒ 3′ ⇒ 4′ (Bass's module, 2.5) ⇒ 1
(T-nilpotence from `p_n ∘ (1 - f_n ∘ t) = 0`; DCC on principal right ideals of each `End X` and of
`End X ⧸ J`, then [Lam-FC, (4.14)]); 4 ⇔ 4′; 3 ⇔ 5 (3.1); 3 ⇔ 6 (2.6, 2.3); 2 ⇒ 2′ ⇒ 1. -/
theorem isLeftPerfect_tfae [Fact (Cardinal.aleph.{v} 1).IsRegular] :
    List.TFAE
      [IsLeftPerfectCategory C,
        ∀ M : LeftModCat.{v} C, HasProjectiveCover M,
        ∀ M : LeftModCat.{v} C, M.IsSemisimple → HasProjectiveCover M,
        ∀ M : LeftModCat.{v} C, M.Flat → Projective M,
        ∀ M : LeftModCat.{v} C, M.Flat → IsCardinalPresentable M (Cardinal.aleph.{v} 1) →
          Projective M,
        ∀ c : C, WellFoundedLT {I : Subobject ((ModCat.yoneda C).obj c) //
          ∃ (d : C) (g : d ⟶ c), I = imageSubobject ((ModCat.yoneda C).map g)},
        ∀ (c : ℕ → C) (f : ∀ i, c (i + 1) ⟶ c i), ∃ n : ℕ, ∀ m : ℕ, n ≤ m →
          ∃ t : (Functor.ofOpSequence f).obj (op n) ⟶ (Functor.ofOpSequence f).obj (op m),
            t ≫ (Functor.ofOpSequence f).map (homOfLE (Nat.zero_le m)).op =
              (Functor.ofOpSequence f).map (homOfLE (Nat.zero_le n)).op,
        ∀ M : LeftModCat.{v} C, M.flatDimension = projectiveDimension M,
        ∀ (J : Type v) [SmallCategory J] [IsFiltered J] (D : J ⥤ LeftModCat.{v} C),
          (∀ j, Projective (D.obj j)) → Projective (colimit D)] :=
  sorry

end TheoremP

section RingTheoremP

variable {A : Type u} [Ring A]

/-- **4.5, rings: the Mares–Simson lemma**: a flat module with a projective cover is projective. -/
theorem Module.BalancedFlat.projective_of_isProjectiveCover {M P : Type*} [AddCommGroup M]
    [Module A M] [AddCommGroup P] [Module A P] [Module.Projective A P]
    (hM : Module.BalancedFlat A M) {p : P →ₗ[A] M} (hp : TauCeti.IsProjectiveCover p) :
    Module.Projective A M :=
  sorry

/-- **4.5, auxiliary**: a ring with zero Jacobson radical and the descending chain condition on
principal right ideals is semisimple ([Lam-FC, (4.14)], cited in the proof of (24.25), not read). -/
theorem isSemisimpleRing_of_wellFoundedLT_isPrincipal (hJ : Ring.jacobson A = ⊥)
    [WellFoundedLT {I : Submodule Aᵐᵒᵖ A // I.IsPrincipal}] : IsSemisimpleRing A :=
  sorry

variable (A) in
/-- **4.5, Bass's Theorem P** ([Bass, Theorem P, pp. 467–468]), derived from `isLeftPerfect_tfae`
at `SingleObj A` through 0.2: the same items, with 4 the descending chain condition on principal
right ideals and 4′ Bass's chain `a₀A ⊇ a₀a₁A ⊇ ⋯`. -/
theorem isLeftPerfectRing_tfae [Fact (Cardinal.aleph.{u} 1).IsRegular] :
    List.TFAE
      [IsLeftPerfectRing A,
        ∀ (M : Type u) [AddCommGroup M] [Module A M], ∃ (P : Type u) (_ : AddCommGroup P)
          (_ : Module A P) (p : P →ₗ[A] M), TauCeti.IsProjectiveCover p,
        ∀ (M : Type u) [AddCommGroup M] [Module A M] [IsSemisimpleModule A M], ∃ (P : Type u)
          (_ : AddCommGroup P) (_ : Module A P) (p : P →ₗ[A] M), TauCeti.IsProjectiveCover p,
        ∀ (M : Type u) [AddCommGroup M] [Module A M], Module.BalancedFlat A M →
          Module.Projective A M,
        ∀ M : ModuleCat.{u} A, Module.BalancedFlat A M →
          IsCardinalPresentable M (Cardinal.aleph.{u} 1) → Module.Projective A M,
        WellFoundedLT {I : Submodule Aᵐᵒᵖ A // I.IsPrincipal},
        ∀ a : ℕ → A, ∃ n, ∀ m ≥ n, Submodule.span Aᵐᵒᵖ {(List.ofFn fun i : Fin m ↦ a i).prod} =
          Submodule.span Aᵐᵒᵖ {(List.ofFn fun i : Fin n ↦ a i).prod},
        ∀ M : ModuleCat.{u} A, flatDimension M = projectiveDimension M,
        ∀ (J : Type u) [SmallCategory J] [IsFiltered J] (D : J ⥤ ModuleCat.{u} A),
          (∀ j, Projective (D.obj j)) → Projective (colimit D)] :=
  sorry

end RingTheoremP

/-! ### 4.6 Global dimension of perfect categories -/

section PerfectGlobalDimension

variable {C : Type u} [Category.{v} C] [Preadditive C] [EssentiallySmall.{v} C]

/-- **4.6** A left perfect `C` has equal left global and weak global dimension (the supremum of
Theorem P (5)). -/
theorem LeftModCat.globalDimension_eq_weakGlobalDimension_of_isLeftPerfectCategory
    [IsLeftPerfectCategory C] :
    Abelian.globalDimension (LeftModCat.{v} C) = LeftModCat.weakGlobalDimension C :=
  sorry

/-- **4.6** If `C` and `Cᵒᵖ` are left perfect, the left and right global dimensions agree (3.3's
symmetry); for instance a semilocal `C` with nilpotent radical (4.3). -/
theorem ModCat.globalDimension_eq_globalDimension_leftModCat_of_isLeftPerfectCategory
    [IsLeftPerfectCategory C] [IsLeftPerfectCategory Cᵒᵖ] :
    Abelian.globalDimension (ModCat.{v} C) = Abelian.globalDimension (LeftModCat.{v} C) :=
  sorry

/-- **4.6, the Bass–Eilenberg criterion** ([Bass, p. 475], credited there to Eilenberg): over a left
perfect `C`, `pd M ≤ n` exactly when `Tor_{n+1}((C ⧸ J)(-, X), M) = 0` for every `X`; so
`pd M = sup {n : Tor_n(C ⧸ J, M) ≠ 0}`. Route: a minimal resolution by covers (4.4) has
differentials into `J · P`, so `Tor_n((C ⧸ J)(-, X), M) = P_n(X) ⧸ (J · P_n)(X)` (0.3), and
`J · P ≠ P` for `P ≠ 0` (4.1). -/
theorem LeftModCat.hasProjectiveDimensionLE_iff_isZero_tor [IsLeftPerfectCategory C]
    (M : LeftModCat.{v} C) (n : ℕ) :
    HasProjectiveDimensionLE M n ↔ ∀ X : C, IsZero (((ModCat.tor ℤ (n + 1)).obj
      (MorphismIdeal.quotientYoneda (TauCeti.jacobsonRadicalIdeal C) X)).obj M) :=
  sorry

/-- **4.6** (agent derivation from the criterion and 3.1) The left global dimension of a left
perfect `C` is the flat dimension of the right module `C ⧸ J`. -/
theorem LeftModCat.globalDimension_eq_iSup_flatDimension_quotientYoneda
    [IsLeftPerfectCategory C] :
    Abelian.globalDimension (LeftModCat.{v} C) =
      ⨆ X : C,
        ModCat.flatDimension (MorphismIdeal.quotientYoneda (TauCeti.jacobsonRadicalIdeal C) X) :=
  sorry

end PerfectGlobalDimension

section RingPerfectGlobalDimension

variable (A : Type u) [Ring A]

/-- **4.6, rings** A left perfect ring has equal left global and weak global dimension. -/
theorem globalDimension_eq_weakGlobalDimension_of_isLeftPerfectRing [Small.{v} A]
    [IsLeftPerfectRing A] : TauCeti.globalDimension.{v} A = weakGlobalDimension.{v} A :=
  sorry

/-- **4.6, rings** A ring that is left and right perfect has equal left and right global
dimension. -/
theorem globalDimension_mulOpposite_of_isLeftPerfectRing [Small.{v} A] [IsLeftPerfectRing A]
    [IsLeftPerfectRing Aᵐᵒᵖ] : TauCeti.globalDimension.{v} Aᵐᵒᵖ = TauCeti.globalDimension.{v} A :=
  sorry

/-- **4.6, rings** For a semiprimary ring the left, right and weak global dimensions agree, with no
Noetherian hypothesis ([Au, Cor. 9, p. 73]; [Lam-LMR, (5.71), p. 188]). -/
theorem globalDimension_mulOpposite_of_isSemiprimaryRing [Small.{v} A] [IsSemiprimaryRing A] :
    TauCeti.globalDimension.{v} Aᵐᵒᵖ = TauCeti.globalDimension.{v} A ∧
      TauCeti.globalDimension.{v} A = weakGlobalDimension.{v} A :=
  sorry

end RingPerfectGlobalDimension

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

/-- **Layer 3 check** A field has weak global dimension `0`. -/
theorem weakGlobalDimension_field (k : Type u) [Field k] : weakGlobalDimension.{u} k = 0 :=
  sorry

/-- **Layer 3 check** The zero ring has weak global dimension `⊥`. -/
theorem weakGlobalDimension_punit : weakGlobalDimension.{u} PUnit.{u + 1} = ⊥ :=
  sorry

/-- **Layer 3 check** `ℤ` has weak and global dimension `1`: `Tor_1^ℤ(ℤ ⧸ 2, ℤ ⧸ 2) ≠ 0`, and
ideals are free. -/
theorem weakGlobalDimension_int :
    weakGlobalDimension.{0} ℤ = 1 ∧ TauCeti.globalDimension.{0} ℤ = 1 :=
  sorry

/-- **Layer 3 check** The dual numbers `k[ε] ⧸ (ε²)` have weak and global dimension `⊤`:
`Tor_n(k, k) ≅ k` for every `n` (Layer 1 checks). -/
theorem weakGlobalDimension_dualNumber (k : Type u) [Field k] :
    weakGlobalDimension.{u} (DualNumber k) = ⊤ ∧ TauCeti.globalDimension.{u} (DualNumber k) = ⊤ :=
  sorry

/-- **Layer 3 check** The upper triangular algebra `T₂(k)` has weak and global dimension `1`. -/
theorem weakGlobalDimension_upperTriangular (k : Type u) [Field k] :
    weakGlobalDimension.{u} (Matrix.blockTriangularSubalgebra k k (id : Fin 2 → Fin 2)) = 1 ∧
      TauCeti.globalDimension.{u} (Matrix.blockTriangularSubalgebra k k (id : Fin 2 → Fin 2)) =
        1 :=
  sorry

/-- **Layer 3 check** The `k`-linear category of the quiver `0 → 1` (Mathlib's `Free k (Fin 2)`)
has global dimension `1`: its category algebra is `T₂(k)` (1.7). -/
theorem globalDimension_free_fin_two (k : Type) [Field k] :
    Abelian.globalDimension (LeftModCat.{0} (CategoryTheory.Free k (Fin 2))) = 1 :=
  sorry

/-- **Layer 4 check** `PowerSeries k` is local, hence semiperfect, and not left perfect. -/
theorem isSemiperfectRing_powerSeries_and_not_isLeftPerfectRing (k : Type u) [Field k] :
    TauCeti.IsSemiperfectRing (PowerSeries k) ∧ ¬ IsLeftPerfectRing (PowerSeries k) :=
  sorry

/-- **Layer 4 check** Bass's module for the constant sequence `X` over `PowerSeries k` is the
Laurent series field: flat (2.5) and not projective. -/
theorem bassRelations_X_linearEquiv_laurentSeries (k : Type u) [Field k] :
    Nonempty (((ℕ →₀ PowerSeries k) ⧸ bassRelations (PowerSeries k) fun _ ↦ PowerSeries.X)
      ≃ₗ[PowerSeries k] LaurentSeries k) ∧
      ¬ Module.Projective (PowerSeries k)
        ((ℕ →₀ PowerSeries k) ⧸ bassRelations (PowerSeries k) fun _ ↦ PowerSeries.X) :=
  sorry

/-- **Layer 4 check** `T₂(k)` is semiprimary, hence left and right perfect. -/
theorem isLeftPerfectRing_upperTriangular (k : Type u) [Field k] :
    IsSemiprimaryRing (Matrix.blockTriangularSubalgebra k k (id : Fin 2 → Fin 2)) ∧
      IsLeftPerfectRing (Matrix.blockTriangularSubalgebra k k (id : Fin 2 → Fin 2)) ∧
      IsLeftPerfectRing (Matrix.blockTriangularSubalgebra k k (id : Fin 2 → Fin 2))ᵐᵒᵖ :=
  sorry

/-- **Layer 4 check** The dual numbers `k[ε] ⧸ (ε²)` are perfect, so flat and projective dimension
agree (Theorem P); both global dimensions are `⊤` (Layer 3 check). -/
theorem isLeftPerfectRing_dualNumber (k : Type u) [Field k] :
    IsLeftPerfectRing (DualNumber k) ∧
      ∀ M : ModuleCat.{u} (DualNumber k), flatDimension M = projectiveDimension M :=
  sorry

/-- The ring `k[x₀, x₁, …] ⧸ (xᵢ xⱼ)`. -/
abbrev squareZeroPolynomialRing (k : Type u) [Field k] : Type u :=
  MvPolynomial ℕ k ⧸
    Ideal.span (Set.range fun p : ℕ × ℕ ↦ (MvPolynomial.X p.1 * MvPolynomial.X p.2 :
      MvPolynomial ℕ k))

/-- **Layer 4 check** `k[x₀, x₁, …] ⧸ (xᵢ xⱼ)` is semiprimary (`J² = 0`, `A ⧸ J = k`), hence
perfect, and not Noetherian. -/
theorem isSemiprimaryRing_squareZeroPolynomialRing (k : Type u) [Field k] :
    IsSemiprimaryRing (squareZeroPolynomialRing k) ∧
      ¬ IsNoetherianRing (squareZeroPolynomialRing k) :=
  sorry

/-- The ring `k[x₀, x₁, …] ⧸ (xᵢ^(i+2), xᵢ xⱼ for i ≠ j)` ([Bass, §3, Example (2), p. 475], with the
variables shifted by one). -/
abbrev bassPolynomialRing (k : Type u) [Field k] : Type u :=
  MvPolynomial ℕ k ⧸
    Ideal.span (Set.range (fun i : ℕ ↦ (MvPolynomial.X i ^ (i + 2) : MvPolynomial ℕ k)) ∪
      {f | ∃ i j : ℕ, i ≠ j ∧ f = MvPolynomial.X i * MvPolynomial.X j})

/-- **Layer 4 check** `bassPolynomialRing k` is perfect and not semiprimary (`xᵢ^(i+1) ≠ 0`), and by
Theorem P its principal ideals satisfy the descending chain condition, although it is not
Noetherian. -/
theorem isLeftPerfectRing_bassPolynomialRing (k : Type u) [Field k] :
    IsLeftPerfectRing (bassPolynomialRing k) ∧ ¬ IsSemiprimaryRing (bassPolynomialRing k) ∧
      WellFoundedLT {I : Ideal (bassPolynomialRing k) // I.IsPrincipal} :=
  sorry

/-- The arrows `i + 1 → i` of the linear `A_∞` category, the `k`-linearization
`CategoryTheory.Free k ℕᵒᵈ` of `(ℕ, ≥)`. -/
noncomputable def aInftyArrow (k : Type) [Field k] (i : ℕ) :
    (CategoryTheory.Free.embedding k ℕᵒᵈ).obj (OrderDual.toDual (i + 1)) ⟶
      (CategoryTheory.Free.embedding k ℕᵒᵈ).obj (OrderDual.toDual i) :=
  (CategoryTheory.Free.embedding k ℕᵒᵈ).map
    (homOfLE (OrderDual.toDual_le_toDual.mpr (Nat.le_succ i)))

/-- **Layer 4 check** The linear `A_∞` category `⋯ → 2 → 1 → 0` is semilocal (every endomorphism
ring is `k`) and not left perfect (the arrows into `0` compose to nonzero paths); its opposite is
left perfect (a radical path strictly lowers the index). -/
theorem isSemilocalCategory_free_orderDual_nat (k : Type) [Field k] :
    IsSemilocalCategory (CategoryTheory.Free k ℕᵒᵈ) ∧
      ¬ IsLeftPerfectCategory (CategoryTheory.Free k ℕᵒᵈ) ∧
      IsLeftPerfectCategory (CategoryTheory.Free k ℕᵒᵈ)ᵒᵖ :=
  sorry

/-- **Layer 4 check** In the linear `A_∞` category, Bass's module of the chain of arrows into `0`
is nonzero and equals `J · B` (4.1). -/
theorem bassModule_free_orderDual_nat (k : Type) [Field k] :
    ¬ IsZero (LeftModCat.bassModule
        (fun i ↦ (CategoryTheory.Free.embedding k ℕᵒᵈ).obj (OrderDual.toDual i)) (aInftyArrow k)) ∧
      ∀ c, MorphismIdeal.smul (TauCeti.jacobsonRadicalIdeal (CategoryTheory.Free k ℕᵒᵈ))
        (LeftModCat.bassModule
          (fun i ↦ (CategoryTheory.Free.embedding k ℕᵒᵈ).obj (OrderDual.toDual i))
          (aInftyArrow k)) c = ⊤ :=
  sorry

/-- **Layer 4 check** The `k`-linear category of the quiver `0 → 1` has `J² = 0`, is left and right
perfect, and `proj C` is Krull–Schmidt; its category algebra is `T₂(k)` (1.7). -/
theorem isLeftPerfectCategory_free_fin_two (k : Type) [Field k] :
    TauCeti.jacobsonRadicalIdeal (CategoryTheory.Free k (Fin 2)) ^ 2 = ⊥ ∧
      IsLeftPerfectCategory (CategoryTheory.Free k (Fin 2)) ∧
      IsLeftPerfectCategory (CategoryTheory.Free k (Fin 2))ᵒᵖ ∧
      TauCeti.IsKrullSchmidt (ModCat.proj (CategoryTheory.Free k (Fin 2))).FullSubcategory :=
  sorry

end TauCetiRoadmap.NoncommutativeFlatness
