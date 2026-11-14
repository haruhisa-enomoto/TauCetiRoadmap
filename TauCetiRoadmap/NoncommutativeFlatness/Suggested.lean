module

import Mathlib
import TauCeti.LinearAlgebra.TensorProduct.Balanced.Basic
import TauCeti.Algebra.Module.CharacterModule.MulOpposite
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

Layers as in `README.md`: 0 the balanced tensor product as a functor; 1 `Tor` over an arbitrary
ring; 2 flat modules; 3 flat dimension and weak global dimension; 4 semiperfect and perfect rings
and Bass's Theorem P.

Conventions (README, "Conventions"): `A` is a ring, not assumed commutative; modules are left
modules; a right `A`-module is a left `Aᵐᵒᵖ`-module; a right ideal of `A` is a
`Submodule Aᵐᵒᵖ A`. The tensor product `M ⊗_A N` of a right module `M` and a left module `N` is
`TauCeti.BalancedTensorProduct ℤ A M N`; the maps `f ⊗ N` and `M ⊗ g` are additive maps, and
`Tor` takes values in `AddCommGrpCat`, which keeps the `Module ℤ` instance of the balanced tensor
product out of the statements. Declarations
that Tau Ceti already has are referred to by their full `TauCeti.` names.

Not stated here, and specified in prose in `README.md`: the swap `M ⊗_A N ≃+ N ⊗_{Aᵐᵒᵖ} M` and
`Tor` swap (they need `N` as a module over `Aᵐᵒᵖᵐᵒᵖ`), the naturality of the isomorphisms, and
the acceptance checks other than those in the last section.
-/

namespace TauCetiRoadmap.NoncommutativeFlatness

open CategoryTheory CategoryTheory.Limits MulOpposite

open scoped CharacterModule DirectSum TensorProduct

universe w v u

/-! ## Layer 0: the balanced tensor product as a functor -/

namespace BalancedTensorProduct

section Maps

variable {A : Type u} [Ring A]
  {M M' M'' : Type*} [AddCommGroup M] [Module Aᵐᵒᵖ M] [AddCommGroup M'] [Module Aᵐᵒᵖ M']
  [AddCommGroup M''] [Module Aᵐᵒᵖ M'']
  {N N' N'' : Type*} [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
  [AddCommGroup N''] [Module A N'']

variable (N) in
/-- **0.1** `f ⊗ N : M ⊗_A N → M' ⊗_A N` for a map `f` of right modules, named after Mathlib's
`LinearMap.rTensor`. -/
def rTensor (f : M →ₗ[Aᵐᵒᵖ] M') :
    TauCeti.BalancedTensorProduct ℤ A M N →+ TauCeti.BalancedTensorProduct ℤ A M' N :=
  (TauCeti.BalancedTensorProduct.map f.toAddMonoidHom.toIntLinearMap LinearMap.id
    (fun a m ↦ f.map_smul (op a) m) (fun _ _ ↦ rfl)).toAddMonoidHom

variable (M) in
/-- **0.1** `M ⊗ g : M ⊗_A N → M ⊗_A N'` for a map `g` of left modules, named after Mathlib's
`LinearMap.lTensor`. -/
def lTensor (g : N →ₗ[A] N') :
    TauCeti.BalancedTensorProduct ℤ A M N →+ TauCeti.BalancedTensorProduct ℤ A M N' :=
  (TauCeti.BalancedTensorProduct.map LinearMap.id g.toAddMonoidHom.toIntLinearMap
    (fun _ _ ↦ rfl) (fun a n ↦ g.map_smul a n)).toAddMonoidHom

@[simp]
theorem rTensor_tmul (f : M →ₗ[Aᵐᵒᵖ] M') (m : M) (n : N) :
    rTensor N f (TauCeti.BalancedTensorProduct.tmul ℤ A m n) =
      TauCeti.BalancedTensorProduct.tmul ℤ A (f m) n :=
  TauCeti.BalancedTensorProduct.map_tmul _ _ _ _ m n

@[simp]
theorem lTensor_tmul (g : N →ₗ[A] N') (m : M) (n : N) :
    lTensor M g (TauCeti.BalancedTensorProduct.tmul ℤ A m n) =
      TauCeti.BalancedTensorProduct.tmul ℤ A m (g n) :=
  TauCeti.BalancedTensorProduct.map_tmul _ _ _ _ m n

theorem rTensor_id : rTensor N (LinearMap.id : M →ₗ[Aᵐᵒᵖ] M) = AddMonoidHom.id _ :=
  AddMonoidHom.ext fun x ↦ by
  induction x using TauCeti.BalancedTensorProduct.induction_on with
  | ht m n => simp
  | ha x y hx hy => simp_all

theorem rTensor_comp (f : M →ₗ[Aᵐᵒᵖ] M') (f' : M' →ₗ[Aᵐᵒᵖ] M'') :
    rTensor N (f' ∘ₗ f) = (rTensor N f').comp (rTensor N f) :=
  AddMonoidHom.ext fun x ↦ by
  induction x using TauCeti.BalancedTensorProduct.induction_on with
  | ht m n => simp
  | ha x y hx hy => simp_all

theorem lTensor_id : lTensor M (LinearMap.id : N →ₗ[A] N) = AddMonoidHom.id _ :=
  AddMonoidHom.ext fun x ↦ by
  induction x using TauCeti.BalancedTensorProduct.induction_on with
  | ht m n => simp
  | ha x y hx hy => simp_all

theorem lTensor_comp (g : N →ₗ[A] N') (g' : N' →ₗ[A] N'') :
    lTensor M (g' ∘ₗ g) = (lTensor M g').comp (lTensor M g) :=
  AddMonoidHom.ext fun x ↦ by
  induction x using TauCeti.BalancedTensorProduct.induction_on with
  | ht m n => simp
  | ha x y hx hy => simp_all

theorem rTensor_comp_lTensor (f : M →ₗ[Aᵐᵒᵖ] M') (g : N →ₗ[A] N') :
    (rTensor N' f).comp (lTensor M g) = (lTensor M' g).comp (rTensor N f) :=
  AddMonoidHom.ext fun x ↦ by
  induction x using TauCeti.BalancedTensorProduct.induction_on with
  | ht m n => simp
  | ha x y hx hy => simp_all

/-- **0.1, right exactness** in the right-module variable. -/
theorem rTensor_exact {f : M →ₗ[Aᵐᵒᵖ] M'} {g : M' →ₗ[Aᵐᵒᵖ] M''} (hfg : Function.Exact f g)
    (hg : Function.Surjective g) : Function.Exact (rTensor N f) (rTensor N g) :=
  sorry

/-- **0.1** Tensoring preserves surjections in the right-module variable. -/
theorem rTensor_surjective {g : M' →ₗ[Aᵐᵒᵖ] M''} (hg : Function.Surjective g) :
    Function.Surjective (rTensor N g) :=
  sorry

/-- **0.1, right exactness** in the left-module variable. -/
theorem lTensor_exact {f : N →ₗ[A] N'} {g : N' →ₗ[A] N''} (hfg : Function.Exact f g)
    (hg : Function.Surjective g) : Function.Exact (lTensor M f) (lTensor M g) :=
  sorry

/-- **0.1** Tensoring preserves surjections in the left-module variable. -/
theorem lTensor_surjective {g : N' →ₗ[A] N''} (hg : Function.Surjective g) :
    Function.Surjective (lTensor M g) :=
  sorry

/-- **0.1, projective factors**: tensoring with a projective right module preserves injections. -/
theorem lTensor_injective_of_projective [Module.Projective Aᵐᵒᵖ M] {g : N →ₗ[A] N'}
    (hg : Function.Injective g) : Function.Injective (lTensor M g) :=
  sorry

/-- **0.1, projective factors**: tensoring with a projective left module preserves injections. -/
theorem rTensor_injective_of_projective [Module.Projective A N] {f : M →ₗ[Aᵐᵒᵖ] M'}
    (hf : Function.Injective f) : Function.Injective (rTensor N f) :=
  sorry

/-- **0.3** The character module of `M ⊗_A N` is `Hom_{Aᵐᵒᵖ}(M, N⁺)`, where `N⁺` is a right module
through Tau Ceti's scoped instance `CharacterModule.instModuleMulOpposite`. -/
noncomputable def characterModuleEquiv (M N : Type*) [AddCommGroup M] [Module Aᵐᵒᵖ M]
    [AddCommGroup N] [Module A N] :
    CharacterModule (TauCeti.BalancedTensorProduct ℤ A M N) ≃+
      (M →ₗ[Aᵐᵒᵖ] CharacterModule N) :=
  sorry

/-- **0.3, Lambek's criterion for one map**: `f ⊗ N` is injective exactly when composition with
`f` is onto on maps into `N⁺`. -/
theorem rTensor_injective_iff_surjective_comp (f : M →ₗ[Aᵐᵒᵖ] M') :
    Function.Injective (rTensor N f) ↔
      Function.Surjective fun φ : M' →ₗ[Aᵐᵒᵖ] CharacterModule N ↦ φ ∘ₗ f :=
  sorry

end Maps

/-- **0.1, commutative rings**: for a commutative ring, with `M` a right module through the same
action (`IsCentralScalar`), the balanced tensor product is Mathlib's tensor product. -/
noncomputable def equivTensorProduct {R : Type u} [CommRing R] (M N : Type*) [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] [AddCommGroup N] [Module R N] :
    TauCeti.BalancedTensorProduct ℤ R M N ≃+ M ⊗[R] N :=
  sorry

@[simp]
theorem equivTensorProduct_tmul {R : Type u} [CommRing R] {M N : Type*} [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] [AddCommGroup N] [Module R N] (m : M)
    (n : N) :
    equivTensorProduct M N (TauCeti.BalancedTensorProduct.tmul ℤ R m n) = m ⊗ₜ[R] n :=
  sorry

variable (A : Type u) [Ring A]

/-- **0.2** The balanced tensor product as a bifunctor
`ModuleCat Aᵐᵒᵖ ⥤ ModuleCat A ⥤ AddCommGrpCat`. -/
noncomputable def functor : ModuleCat.{v} Aᵐᵒᵖ ⥤ ModuleCat.{v} A ⥤ AddCommGrpCat.{v} where
  obj M :=
    { obj N := AddCommGrpCat.of (TauCeti.BalancedTensorProduct ℤ A M N)
      map g := AddCommGrpCat.ofHom (lTensor M g.hom)
      map_id N := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x ↦
        DFunLike.congr_fun (lTensor_id (M := M) (N := N)) x)
      map_comp f g := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x ↦
        DFunLike.congr_fun (lTensor_comp (M := M) f.hom g.hom) x) }
  map f :=
    { app N := AddCommGrpCat.ofHom (rTensor N f.hom)
      naturality _ _ g := AddCommGrpCat.hom_ext (rTensor_comp_lTensor f.hom g.hom) }
  map_id M := NatTrans.ext (funext fun N ↦ AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x ↦
    DFunLike.congr_fun (rTensor_id (M := M) (N := N)) x))
  map_comp f g := NatTrans.ext (funext fun N ↦ AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x ↦
    DFunLike.congr_fun (rTensor_comp (N := N) f.hom g.hom) x))

/-- **0.2** The bifunctor is additive in the left-module variable. -/
instance (M : ModuleCat.{v} Aᵐᵒᵖ) : ((functor A).obj M).Additive :=
  sorry

/-- **0.2** The bifunctor is additive in the right-module variable. -/
instance (N : ModuleCat.{v} A) : ((functor A).flip.obj N).Additive :=
  sorry

end BalancedTensorProduct

/-! ## Layer 1: `Tor` over an arbitrary ring -/

/-- **1.1** `Small.{v} Aᵐᵒᵖ` from `Small.{v} A`, so that right modules have projective
resolutions in `ModuleCat.{v} Aᵐᵒᵖ`. -/
instance small_mulOpposite (A : Type u) [Small.{v} A] : Small.{v} Aᵐᵒᵖ :=
  small_of_injective MulOpposite.unop_injective

section Tor

variable (A : Type u) [Ring A] [Small.{v} A]

/-- **1.1** `Tor_n^A(M, N)`, derived in the left-module variable `N`, the shape of Mathlib's
`CategoryTheory.Tor`. -/
noncomputable def BalancedTor (n : ℕ) :
    ModuleCat.{v} Aᵐᵒᵖ ⥤ ModuleCat.{v} A ⥤ AddCommGrpCat.{v} where
  obj M := ((BalancedTensorProduct.functor A).obj M).leftDerived n
  map f := NatTrans.leftDerived ((BalancedTensorProduct.functor A).map f) n

/-- **1.1** `Tor_n^A(M, N)`, derived in the right-module variable `M`, the shape of Mathlib's
`CategoryTheory.Tor'`. -/
noncomputable def BalancedTor' (n : ℕ) :
    ModuleCat.{v} Aᵐᵒᵖ ⥤ ModuleCat.{v} A ⥤ AddCommGrpCat.{v} :=
  Functor.flip
    { obj N := ((BalancedTensorProduct.functor A).flip.obj N).leftDerived n
      map g := NatTrans.leftDerived ((BalancedTensorProduct.functor A).flip.map g) n }

/-- **1.1** `Tor_0` is the tensor product. -/
noncomputable def balancedTorZeroIso :
    BalancedTor.{v} A 0 ≅ BalancedTensorProduct.functor.{v} A :=
  sorry

/-- **1.1** `Tor'_0` is the tensor product. -/
noncomputable def balancedTor'ZeroIso :
    BalancedTor'.{v} A 0 ≅ BalancedTensorProduct.functor.{v} A :=
  sorry

variable {A}

/-- **1.1** Higher `Tor` vanishes at a projective left module. -/
theorem isZero_balancedTor_succ_of_projective (M : ModuleCat.{v} Aᵐᵒᵖ) (N : ModuleCat.{v} A)
    [Projective N] (n : ℕ) : IsZero (((BalancedTor A (n + 1)).obj M).obj N) :=
  sorry

/-- **1.1** Higher `Tor'` vanishes at a projective right module. -/
theorem isZero_balancedTor'_succ_of_projective (M : ModuleCat.{v} Aᵐᵒᵖ) [Projective M]
    (N : ModuleCat.{v} A) (n : ℕ) : IsZero (((BalancedTor' A (n + 1)).obj M).obj N) :=
  sorry

section LongExact

variable {S : ShortComplex (ModuleCat.{v} Aᵐᵒᵖ)}

/-- **1.2** The connecting map `Tor_{n+1}(M₃, N) → Tor_n(M₁, N)` of a short exact sequence of
right modules. -/
noncomputable def ShortComplex.ShortExact.balancedTorδ (hS : S.ShortExact) (N : ModuleCat.{v} A)
    (n : ℕ) :
    ((BalancedTor A (n + 1)).obj S.X₃).obj N ⟶ ((BalancedTor A n).obj S.X₁).obj N :=
  sorry

/-- **1.2** Exactness at `Tor_n(M₁, N)`. -/
theorem balancedTor_exact₁ (hS : S.ShortExact) (N : ModuleCat.{v} A) (n : ℕ) :
    Function.Exact (ShortComplex.ShortExact.balancedTorδ hS N n).hom
      (((BalancedTor A n).map S.f).app N).hom :=
  sorry

/-- **1.2** Exactness at `Tor_n(M₂, N)`. -/
theorem balancedTor_exact₂ (hS : S.ShortExact) (N : ModuleCat.{v} A) (n : ℕ) :
    Function.Exact (((BalancedTor A n).map S.f).app N).hom
      (((BalancedTor A n).map S.g).app N).hom :=
  sorry

/-- **1.2** Exactness at `Tor_{n+1}(M₃, N)`. -/
theorem balancedTor_exact₃ (hS : S.ShortExact) (N : ModuleCat.{v} A) (n : ℕ) :
    Function.Exact (((BalancedTor A (n + 1)).map S.g).app N).hom
      (ShortComplex.ShortExact.balancedTorδ hS N n).hom :=
  sorry

end LongExact

variable (A) in
/-- **1.3, balance**: the two derivations of `Tor` agree. -/
noncomputable def balancedTorIso (n : ℕ) : BalancedTor.{v} A n ≅ BalancedTor'.{v} A n :=
  sorry

/-- **1.4, commutative rings**: over a commutative ring, `BalancedTor` is Mathlib's
`CategoryTheory.Tor` on underlying abelian groups. -/
noncomputable def balancedTorIsoTor (R : Type u) [CommRing R] (n : ℕ) :
    ModuleCat.restrictScalars.{u} (RingEquiv.toOpposite R).symm.toRingHom ⋙ BalancedTor.{u} R n ≅
      Tor (ModuleCat.{u} R) n ⋙
        (Functor.whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) :=
  sorry

/-- **1.4, cyclic modules**: for a right ideal `I` and a left ideal `K`,
`Tor_1^A(A ⧸ I, A ⧸ K) ≃+ (I ∩ K) ⧸ IK`, with `IK` the additive subgroup generated by products. -/
noncomputable def balancedTorOneQuotientEquiv (A : Type u) [Ring A] (I : Submodule Aᵐᵒᵖ A)
    (K : Ideal A) :
    (((BalancedTor.{u} A 1).obj (ModuleCat.of Aᵐᵒᵖ (A ⧸ I))).obj (ModuleCat.of A (A ⧸ K))) ≃+
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
    (N : Submodule Aᵐᵒᵖ P) : N.FG → Function.Injective (BalancedTensorProduct.rTensor M N.subtype)

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
            Function.Injective (BalancedTensorProduct.rTensor M i),
        ∀ I : Submodule Aᵐᵒᵖ A, I.FG →
          Function.Injective (BalancedTensorProduct.rTensor M I.subtype),
        Module.Injective Aᵐᵒᵖ (CharacterModule M),
        ∀ N : ModuleCat.{v} Aᵐᵒᵖ, IsZero (((BalancedTor.{v} A 1).obj N).obj (ModuleCat.of A M)),
        ∀ I : Submodule Aᵐᵒᵖ A, I.FG →
          IsZero (((BalancedTor.{v} A 1).obj (ModuleCat.of Aᵐᵒᵖ (Shrink.{v} (A ⧸ I)))).obj
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
    IsZero (((BalancedTor A (n + 1)).obj N).obj M) :=
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
    IsZero (((BalancedTor.{v} A i).obj N).obj M)

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
      IsZero (((BalancedTor.{v} A (n + 1)).obj (ModuleCat.of Aᵐᵒᵖ (Shrink.{v} (A ⧸ I)))).obj M) :=
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
        IsZero (((BalancedTor.{v} A (n + 1)).obj N).obj M) :=
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
